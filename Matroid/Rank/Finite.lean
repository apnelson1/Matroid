import Matroid.Rank.ENat

variable {α ι : Type*} {M : Matroid α} {X X' Y Y' I : Set α} {e : α}

open Set

namespace Matroid

section rFin

def rFin (M : Matroid α) (X : Set α) :=
  M.eRk X < ⊤

@[simp] lemma eRk_lt_top_iff : M.eRk X < ⊤ ↔ M.rFin X := Iff.rfl

@[simp] lemma eRk_ne_top_iff : M.eRk X ≠ ⊤ ↔ M.rFin X :=
  by rw [rFin, ← lt_top_iff_ne_top]

lemma rFin.ne (h : M.rFin X) : M.eRk X ≠ ⊤ :=
  eRk_ne_top_iff.2 h

lemma rFin.lt (h : M.rFin X) : M.eRk X < ⊤ :=
  h

lemma eRk_eq_top_iff : M.eRk X = ⊤ ↔ ¬M.rFin X := by rw [← eRk_ne_top_iff, not_ne_iff]

@[simp] lemma rFin_inter_ground_iff : M.rFin (X ∩ M.E) ↔ M.rFin X := by
  rw [rFin, eRk_inter_ground, rFin]

lemma rFin.to_inter_ground (h : M.rFin X) : M.rFin (X ∩ M.E) :=
  rFin_inter_ground_iff.2 h

lemma rFin.finite_of_basis' (h : M.rFin X) (hI : M.Basis' I X) : I.Finite := by
  rwa [← encard_lt_top_iff, hI.encard]

lemma rFin.finite_of_basis (h : M.rFin X) (hI : M.Basis I X) : I.Finite := by
  rwa [← encard_lt_top_iff, hI.encard]

lemma Basis'.finite_of_rFin (hI : M.Basis' I X) (h : M.rFin X) : I.Finite :=
  h.finite_of_basis' hI

lemma Basis.finite_of_rFin (hI : M.Basis I X) (h : M.rFin X) : I.Finite :=
  h.finite_of_basis hI

lemma rFin_iff' : M.rFin X ↔ ∃ I, M.Basis' I X ∧ I.Finite :=
  ⟨fun h ↦ (M.exists_basis' X).elim (fun I hI ↦ ⟨I, hI, h.finite_of_basis' hI⟩),
    fun ⟨I, hI, hIfin⟩ ↦ by rwa [← eRk_lt_top_iff, hI.eRk_eq_encard, encard_lt_top_iff]⟩

lemma rFin_iff (hX : X ⊆ M.E := by aesop_mat) : M.rFin X ↔ ∃ I, M.Basis I X ∧ I.Finite := by
  simp_rw [rFin_iff', M.basis'_iff_basis hX]

lemma rFin.exists_finite_basis' (h : M.rFin X) : ∃ I, M.Basis' I X ∧ I.Finite :=
  rFin_iff'.1 h

lemma rFin.exists_finite_basis (h : M.rFin X) (hX : X ⊆ M.E := by aesop_mat) :
    ∃ I, M.Basis I X ∧ I.Finite :=
  (rFin_iff hX).1 h

lemma rFin.exists_finset_basis' (h : M.rFin X) : ∃ (I : Finset α), M.Basis' I X := by
  obtain ⟨I, hI, hfin⟩ := h.exists_finite_basis'
  exact ⟨hfin.toFinset, by simpa⟩

lemma rFin.exists_finset_basis (h : M.rFin X) (hX : X ⊆ M.E := by aesop_mat) :
    ∃ (I : Finset α), M.Basis I X := by
  obtain ⟨I, hI, hfin⟩ := h.exists_finite_basis
  exact ⟨hfin.toFinset, by simpa⟩

lemma Basis'.rFin_of_finite (hIX : M.Basis' I X) (h : I.Finite) : M.rFin X := by
  rwa [← eRk_ne_top_iff, ← hIX.encard, encard_ne_top_iff]

lemma Basis'.rFin_iff_finite (hIX : M.Basis' I X) : M.rFin X ↔ I.Finite :=
  ⟨hIX.finite_of_rFin, hIX.rFin_of_finite⟩

lemma Basis.rFin_of_finite (hIX : M.Basis I X) (h : I.Finite) : M.rFin X := by
  rwa [← eRk_ne_top_iff, ← hIX.encard, encard_ne_top_iff]

lemma Basis.rFin_iff_finite (hIX : M.Basis I X) : M.rFin X ↔ I.Finite :=
  ⟨hIX.finite_of_rFin, hIX.rFin_of_finite⟩

lemma Indep.rFin_iff_finite (hI : M.Indep I) : M.rFin I ↔ I.Finite :=
  hI.basis_self.rFin_iff_finite

lemma Indep.finite_of_rFin (hI : M.Indep I) (hfin : M.rFin I) : I.Finite :=
  hI.basis_self.finite_of_rFin hfin

lemma rFin_of_finite (M : Matroid α) (hX : X.Finite) : M.rFin X :=
  (M.eRk_le_encard X).trans_lt (encard_lt_top_iff.mpr hX)

lemma Indep.subset_finite_basis'_of_subset_of_rFin (hI : M.Indep I) (hIX : I ⊆ X)
    (hX : M.rFin X) : ∃ J, M.Basis' J X ∧ I ⊆ J ∧ J.Finite :=
  (hI.subset_basis'_of_subset hIX).imp fun _ hJ => ⟨hJ.1, hJ.2, hJ.1.finite_of_rFin hX⟩

lemma Indep.subset_finite_basis_of_subset_of_rFin (hI : M.Indep I) (hIX : I ⊆ X)
    (hX : M.rFin X) (hXE : X ⊆ M.E := by aesop_mat) : ∃ J, M.Basis J X ∧ I ⊆ J ∧ J.Finite :=
  (hI.subset_basis_of_subset hIX).imp fun _ hJ => ⟨hJ.1, hJ.2, hJ.1.finite_of_rFin hX⟩

lemma rFin_singleton (M : Matroid α) (e : α) : M.rFin {e} :=
  M.rFin_of_finite (finite_singleton e)

@[simp] lemma rFin_empty (M : Matroid α) : M.rFin ∅ :=
  M.rFin_of_finite finite_empty

lemma rFin.subset (h : M.rFin Y) (hXY : X ⊆ Y) : M.rFin X :=
  (M.eRk_mono hXY).trans_lt h

lemma not_rFin_superset (h : ¬M.rFin X) (hXY : X ⊆ Y) : ¬M.rFin Y :=
  fun h' ↦ h (h'.subset hXY)

lemma not_rFin_of_eRk_ge (h : ¬M.rFin X) (hXY : M.eRk X ≤ M.eRk Y) : ¬M.rFin Y :=
  fun h' ↦ h (hXY.trans_lt h')

lemma rFin.finite_of_indep_subset (hX : M.rFin X) (hI : M.Indep I) (hIX : I ⊆ X) : I.Finite :=
  hI.finite_of_rFin (hX.to_inter_ground.subset (subset_inter hIX hI.subset_ground))

@[simp] lemma rFin_ground_iff_finiteRk : M.rFin M.E ↔ M.FiniteRk := by
  obtain ⟨B, hB⟩ := M.exists_base
  use fun h => ⟨⟨B, hB, h.finite_of_indep_subset hB.indep hB.subset_ground⟩⟩
  simp_rw [rFin_iff (rfl.subset), basis_ground_iff]
  exact fun ⟨h⟩ ↦ h

lemma rFin_ground (M : Matroid α) [FiniteRk M] : M.rFin M.E := by
  rwa [rFin_ground_iff_finiteRk]

lemma eRank_lt_top (M : Matroid α) [FiniteRk M] : M.eRank < ⊤ := by
  rw [eRank_def, eRk_lt_top_iff]; exact M.rFin_ground

lemma Indep.finite_of_subset_rFin (hI : M.Indep I) (hIX : I ⊆ X) (hX : M.rFin X) : I.Finite :=
  hX.finite_of_indep_subset hI hIX

lemma rFin.indep_of_encard_le_eRk (hX : M.rFin I) (h : encard I ≤ M.eRk I) : M.Indep I := by
  rw [indep_iff_eRk_eq_encard_of_finite _]
  · exact (M.eRk_le_encard I).antisymm h
  simpa using h.trans_lt hX.lt

lemma rFin.to_closure (h : M.rFin X) : M.rFin (M.closure X) := by
  rwa [← eRk_lt_top_iff, eRk_closure_eq]

@[simp] lemma rFin_closure_iff : M.rFin (M.closure X) ↔ M.rFin X := by
  rw [← eRk_ne_top_iff, eRk_closure_eq, eRk_ne_top_iff]

lemma rFin.union (hX : M.rFin X) (hY : M.rFin Y) : M.rFin (X ∪ Y) := by
  rw [← eRk_lt_top_iff] at *
  apply (M.eRk_union_le_eRk_add_eRk X Y).trans_lt
  rw [WithTop.add_lt_top]
  exact ⟨hX, hY⟩

lemma rFin.rFin_union_iff (hX : M.rFin X) : M.rFin (X ∪ Y) ↔ M.rFin Y :=
  ⟨fun h ↦ h.subset subset_union_right, fun h ↦ hX.union h⟩

lemma rFin.rFin_diff_iff (hX : M.rFin X) : M.rFin (Y \ X) ↔ M.rFin Y := by
  rw [← hX.rFin_union_iff, union_diff_self, hX.rFin_union_iff]

lemma rFin.inter_right (hX : M.rFin X) (Y : Set α) : M.rFin (X ∩ Y) :=
  hX.subset inter_subset_left

lemma rFin.inter_left (hX : M.rFin X) (Y : Set α) : M.rFin (Y ∩ X) :=
  hX.subset inter_subset_right

lemma rFin.diff (hX : M.rFin X) (D : Set α) : M.rFin (X \ D) :=
  hX.subset diff_subset

lemma rFin.insert (hX : M.rFin X) (e : α) : M.rFin (insert e X) := by
  rw [← union_singleton]; exact hX.union (M.rFin_singleton e)

@[simp] lemma rFin_insert_iff : M.rFin (insert e X) ↔ M.rFin X := by
  rw [← singleton_union, (M.rFin_singleton e).rFin_union_iff]

@[simp] lemma rFin_diff_singleton_iff : M.rFin (X \ {e}) ↔ M.rFin X := by
  rw [(M.rFin_singleton e).rFin_diff_iff]

lemma to_rFin (M : Matroid α) [FiniteRk M] (X : Set α) : M.rFin X := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  rw [← eRk_lt_top_iff, hI.eRk_eq_encard, encard_lt_top_iff]
  exact hI.indep.finite_of_subset_rFin hI.indep.subset_ground M.rFin_ground

lemma rFin.closure_eq_closure_of_subset_of_eRk_ge_eRk (hX : M.rFin X) (hXY : X ⊆ Y)
    (hr : M.eRk Y ≤ M.eRk X) : M.closure X = M.closure Y := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis'_of_subset (hI.subset.trans hXY)
  rw [hI.eRk_eq_encard, hJ.eRk_eq_encard] at hr
  rw [← closure_inter_ground, ← M.closure_inter_ground Y,
    ← hI.basis_inter_ground.closure_eq_closure,
    ← hJ.basis_inter_ground.closure_eq_closure, Finite.eq_of_subset_of_encard_le'
      (hI.indep.finite_of_subset_rFin hI.subset hX) hIJ hr]

lemma eRk_union_eq_of_subset_of_eRk_le_eRk (Z : Set α) (hXY : X ⊆ Y) (hr : M.eRk Y ≤ M.eRk X) :
    M.eRk (X ∪ Z) = M.eRk (Y ∪ Z) := by
  obtain hX' | hX' := em (M.rFin X)
  · rw [← eRk_union_closure_left_eq, hX'.closure_eq_closure_of_subset_of_eRk_ge_eRk hXY hr,
      eRk_union_closure_left_eq]
  rw [eRk_eq_top_iff.2, eRk_eq_top_iff.2]
  · exact not_rFin_of_eRk_ge hX' (M.eRk_mono (subset_union_of_subset_left hXY _))
  exact not_rFin_of_eRk_ge hX' (M.eRk_mono subset_union_left)

lemma eRk_union_eq_of_subsets_of_eRks_le (hX : X ⊆ X') (hY : Y ⊆ Y') (hXX' : M.eRk X' ≤ M.eRk X)
    (hYY' : M.eRk Y' ≤ M.eRk Y) : M.eRk (X ∪ Y) = M.eRk (X' ∪ Y') := by
  rw [eRk_union_eq_of_subset_of_eRk_le_eRk _ hX hXX', union_comm,
    eRk_union_eq_of_subset_of_eRk_le_eRk _ hY hYY', union_comm]

lemma rFin.basis_of_subset_closure_of_subset_of_encard_le (hX : M.rFin X) (hXI : X ⊆ M.closure I)
    (hIX : I ⊆ X) (hI : I.encard ≤ M.eRk X) : M.Basis I X := by
  obtain ⟨J, hJ⟩ := M.exists_basis (I ∩ M.E)
  have hIJ := hJ.subset.trans inter_subset_left
  rw [← closure_inter_ground] at hXI
  replace hXI := hXI.trans <| M.closure_subset_closure_of_subset_closure hJ.subset_closure
  have hJX := hJ.indep.basis_of_subset_of_subset_closure (hIJ.trans hIX) hXI
  rw [← hJX.encard] at hI
  rwa [← Finite.eq_of_subset_of_encard_le' (hX.finite_of_basis hJX) hIJ hI]

lemma rFin.iUnion [Fintype ι] {Xs : ι → Set α} (h : ∀ i, M.rFin (Xs i)) : M.rFin (⋃ i, Xs i) := by
  choose Is hIs using fun i ↦ M.exists_basis' (Xs i)
  have hfin : (⋃ i, Is i).Finite := finite_iUnion <| fun i ↦ (h i).finite_of_basis' (hIs i)
  rw [← rFin_closure_iff, ← M.closure_iUnion_closure_eq_closure_iUnion]
  simp_rw [← (hIs _).closure_eq_closure, M.closure_iUnion_closure_eq_closure_iUnion]
  exact (M.rFin_of_finite hfin).to_closure

lemma eRk_eq_iSup_finset_eRk (M : Matroid α) (X : Set α) :
    M.eRk X = ⨆ Y ∈ {S : Finset α | (S : Set α) ⊆ X}, M.eRk Y := by
  simp only [mem_setOf_eq, le_antisymm_iff, iSup_le_iff]
  refine ⟨?_, fun S hSX ↦ M.eRk_mono hSX⟩

  by_cases hX : M.rFin X
  · obtain ⟨I, hI⟩ := hX.exists_finset_basis'
    exact le_iSup₂_of_le (i := I) hI.subset <| by rw [hI.er]

  obtain ⟨I, hI⟩ := M.exists_basis' X
  rw [← eRk_eq_top_iff] at hX
  rw [hX, top_le_iff, ← WithTop.forall_ge_iff_eq_top]
  intro n
  rw [hI.eRk_eq_encard, encard_eq_top_iff] at hX
  obtain ⟨J, hJI, rfl⟩ := hX.exists_subset_card_eq n
  apply le_iSup₂_of_le J (hJI.trans hI.subset)
  rw [(hI.indep.subset hJI).er, encard_coe_eq_coe_finsetCard]
  rfl

end rFin
