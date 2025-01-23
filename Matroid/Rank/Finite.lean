import Matroid.Rank.ENat

variable {α ι : Type*} {M : Matroid α} {X X' Y Y' I : Set α} {e : α}

open Set

namespace Matroid

section rFin

def rFin (M : Matroid α) (X : Set α) :=
  M.er X < ⊤

@[simp] lemma er_lt_top_iff : M.er X < ⊤ ↔ M.rFin X := Iff.rfl

@[simp] lemma er_ne_top_iff : M.er X ≠ ⊤ ↔ M.rFin X :=
  by rw [rFin, ← lt_top_iff_ne_top]

lemma rFin.ne (h : M.rFin X) : M.er X ≠ ⊤ :=
  er_ne_top_iff.2 h

lemma rFin.lt (h : M.rFin X) : M.er X < ⊤ :=
  h

lemma er_eq_top_iff : M.er X = ⊤ ↔ ¬M.rFin X := by rw [← er_ne_top_iff, not_ne_iff]

@[simp] lemma rFin_inter_ground_iff : M.rFin (X ∩ M.E) ↔ M.rFin X := by
  rw [rFin, er_inter_ground, rFin]

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
    fun ⟨I, hI, hIfin⟩ ↦ by rwa [← er_lt_top_iff, hI.er_eq_encard, encard_lt_top_iff]⟩

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
  rwa [← er_ne_top_iff, ← hIX.encard, encard_ne_top_iff]

lemma Basis'.rFin_iff_finite (hIX : M.Basis' I X) : M.rFin X ↔ I.Finite :=
  ⟨hIX.finite_of_rFin, hIX.rFin_of_finite⟩

lemma Basis.rFin_of_finite (hIX : M.Basis I X) (h : I.Finite) : M.rFin X := by
  rwa [← er_ne_top_iff, ← hIX.encard, encard_ne_top_iff]

lemma Basis.rFin_iff_finite (hIX : M.Basis I X) : M.rFin X ↔ I.Finite :=
  ⟨hIX.finite_of_rFin, hIX.rFin_of_finite⟩

lemma Indep.rFin_iff_finite (hI : M.Indep I) : M.rFin I ↔ I.Finite :=
  hI.basis_self.rFin_iff_finite

lemma Indep.finite_of_rFin (hI : M.Indep I) (hfin : M.rFin I) : I.Finite :=
  hI.basis_self.finite_of_rFin hfin

lemma rFin_of_finite (M : Matroid α) (hX : X.Finite) : M.rFin X :=
  (M.er_le_encard X).trans_lt (encard_lt_top_iff.mpr hX)

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
  (M.er_mono hXY).trans_lt h

lemma not_rFin_superset (h : ¬M.rFin X) (hXY : X ⊆ Y) : ¬M.rFin Y :=
  fun h' ↦ h (h'.subset hXY)

lemma not_rFin_of_er_ge (h : ¬M.rFin X) (hXY : M.er X ≤ M.er Y) : ¬M.rFin Y :=
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

lemma erk_lt_top (M : Matroid α) [FiniteRk M] : M.erk < ⊤ := by
  rw [erk_def, er_lt_top_iff]; exact M.rFin_ground

lemma Indep.finite_of_subset_rFin (hI : M.Indep I) (hIX : I ⊆ X) (hX : M.rFin X) : I.Finite :=
  hX.finite_of_indep_subset hI hIX

lemma rFin.indep_of_encard_le_er (hX : M.rFin I) (h : encard I ≤ M.er I) : M.Indep I := by
  rw [indep_iff_er_eq_encard_of_finite _]
  · exact (M.er_le_encard I).antisymm h
  simpa using h.trans_lt hX.lt

lemma rFin.to_closure (h : M.rFin X) : M.rFin (M.closure X) := by
  rwa [← er_lt_top_iff, er_closure_eq]

@[simp] lemma rFin_closure_iff : M.rFin (M.closure X) ↔ M.rFin X := by
  rw [← er_ne_top_iff, er_closure_eq, er_ne_top_iff]

lemma rFin.union (hX : M.rFin X) (hY : M.rFin Y) : M.rFin (X ∪ Y) := by
  rw [← er_lt_top_iff] at *
  apply (M.er_union_le_er_add_er X Y).trans_lt
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
  rw [← er_lt_top_iff, hI.er_eq_encard, encard_lt_top_iff]
  exact hI.indep.finite_of_subset_rFin hI.indep.subset_ground M.rFin_ground

lemma rFin.closure_eq_closure_of_subset_of_er_ge_er (hX : M.rFin X) (hXY : X ⊆ Y)
    (hr : M.er Y ≤ M.er X) : M.closure X = M.closure Y := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis'_of_subset (hI.subset.trans hXY)
  rw [hI.er_eq_encard, hJ.er_eq_encard] at hr
  rw [← closure_inter_ground, ← M.closure_inter_ground Y,
    ← hI.basis_inter_ground.closure_eq_closure,
    ← hJ.basis_inter_ground.closure_eq_closure, Finite.eq_of_subset_of_encard_le'
      (hI.indep.finite_of_subset_rFin hI.subset hX) hIJ hr]

lemma er_union_eq_of_subset_of_er_le_er (Z : Set α) (hXY : X ⊆ Y) (hr : M.er Y ≤ M.er X) :
    M.er (X ∪ Z) = M.er (Y ∪ Z) := by
  obtain hX' | hX' := em (M.rFin X)
  · rw [← er_union_closure_left_eq, hX'.closure_eq_closure_of_subset_of_er_ge_er hXY hr,
      er_union_closure_left_eq]
  rw [er_eq_top_iff.2, er_eq_top_iff.2]
  · exact not_rFin_of_er_ge hX' (M.er_mono (subset_union_of_subset_left hXY _))
  exact not_rFin_of_er_ge hX' (M.er_mono subset_union_left)

lemma er_union_eq_of_subsets_of_ers_le (hX : X ⊆ X') (hY : Y ⊆ Y') (hXX' : M.er X' ≤ M.er X)
    (hYY' : M.er Y' ≤ M.er Y) : M.er (X ∪ Y) = M.er (X' ∪ Y') := by
  rw [er_union_eq_of_subset_of_er_le_er _ hX hXX', union_comm,
    er_union_eq_of_subset_of_er_le_er _ hY hYY', union_comm]

lemma rFin.basis_of_subset_closure_of_subset_of_encard_le (hX : M.rFin X) (hXI : X ⊆ M.closure I)
    (hIX : I ⊆ X) (hI : I.encard ≤ M.er X) : M.Basis I X := by
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

lemma er_eq_iSup_finset_er (M : Matroid α) (X : Set α) :
    M.er X = ⨆ Y ∈ {S : Finset α | (S : Set α) ⊆ X}, M.er Y := by
  simp only [mem_setOf_eq, le_antisymm_iff, iSup_le_iff]
  refine ⟨?_, fun S hSX ↦ M.er_mono hSX⟩

  by_cases hX : M.rFin X
  · obtain ⟨I, hI⟩ := hX.exists_finset_basis'
    exact le_iSup₂_of_le (i := I) hI.subset <| by rw [hI.er]

  obtain ⟨I, hI⟩ := M.exists_basis' X
  rw [← er_eq_top_iff] at hX
  rw [hX, top_le_iff, ← WithTop.forall_ge_iff_eq_top]
  intro n
  rw [hI.er_eq_encard, encard_eq_top_iff] at hX
  obtain ⟨J, hJI, rfl⟩ := hX.exists_subset_card_eq n
  apply le_iSup₂_of_le J (hJI.trans hI.subset)
  rw [(hI.indep.subset hJI).er, encard_coe_eq_coe_finsetCard]
  rfl

end rFin
