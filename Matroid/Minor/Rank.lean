import Matroid.Minor.Basic
import Matroid.ForMathlib.ENat

open Set

namespace Matroid

variable {α : Type*} {M N : Matroid α} {I J C D X Y Z : Set α} {e f : α}

section Delete

@[simp] lemma delete_eRk_eq' (M : Matroid α) (D X : Set α) : (M ＼ D).eRk X = M.eRk (X \ D) := by
  rw [← restrict_compl, restrict_eRk_eq', diff_eq, inter_comm M.E, ← inter_assoc, ← diff_eq,
    eRk_inter_ground]

lemma delete_eRk_eq (M : Matroid α) (h : Disjoint X D) : (M ＼ D).eRk X = M.eRk X := by
  rwa [delete_eRk_eq', sdiff_eq_left.2]

lemma delete_eRk_eq_delete_eRk_diff (M : Matroid α) (D X : Set α) :
    (M ＼ D).eRk X = (M ＼ D).eRk (X \ D) := by
  simp

@[simp] lemma delete_rFin_iff : (M ＼ D).rFin X ↔ M.rFin (X \ D) := by
  rw [← eRk_lt_top_iff, delete_eRk_eq', eRk_lt_top_iff]

lemma Coindep.delete_eRank_eq (hX : M.Coindep X) : (M ＼ X).eRank = M.eRank := by
  rw [coindep_iff_closure_compl_eq_ground] at hX
  rw [eRank_def, delete_ground, delete_eRk_eq', diff_diff, union_self, ← eRk_closure_eq, hX,
    eRank_def]

lemma eRank_delete_le (M : Matroid α) (D : Set α) : (M ＼ D).eRank ≤ M.eRank := by
  rw [eRank_def, delete_ground, delete_eRk_eq', diff_diff, union_self, eRank_def]
  exact M.eRk_mono diff_subset

lemma Indep.delete_eRank_dual_eq (hI : M.Indep I) : (M ／ I)✶.eRank = M✶.eRank := by
  rw [← hI.coindep.delete_eRank_eq, contract_dual_eq_dual_delete]

lemma Indep.eRank_dual_restrict_eq (hI : M.Indep I) : (M ↾ I)✶.eRank = 0 := by
  simp [hI.restrict_eq_freeOn]

lemma Basis.eRank_dual_restrict_of_disjoint (hB : M.Basis I (I ∪ X)) (hdj : Disjoint I X) :
    (M ↾ (I ∪ X))✶.eRank = X.encard := by
  rw [← Base.encard_compl_eq hB.restrict_base]; simp [hdj.sdiff_eq_right]

lemma Basis.eRank_dual_restrict (hB : M.Basis I X) : (M ↾ X)✶.eRank = (X \ I).encard := by
  rw [← Base.encard_compl_eq hB.restrict_base, restrict_ground_eq]

@[simp] lemma eRank_dual_restrict_eq_zero_iff : (M ↾ I)✶.eRank = 0 ↔ M.Indep I := by
  rw [← restrict_eq_freeOn_iff, eRank_eq_zero_iff, dual_ground, restrict_ground_eq,
    eq_comm, eq_dual_comm, loopyOn_dual_eq]

lemma Indep.contract_eRk_dual_eq (hI : M.Indep I) : (M ／ I)✶.eRank = M✶.eRank := by
  rw [contract_dual_eq_dual_delete, hI.coindep.delete_eRank_eq]

end Delete

/-- The relative rank of sets `X` and `Y`, defined to be the rank of `Y` in `M ／ X`,
and equal to the minimum number of elements that need to be added to `X` to span `Y`.
The definition suggests that `X` and `Y` should be disjoint, but it is also a natural
expression when `X ⊆ Y`, and sometimes more generally. -/
noncomputable def relRank (M : Matroid α) (X Y : Set α) : ℕ∞ := (M ／ X).eRk Y

lemma relRank_eq_eRk_contract (M : Matroid α) (X Y : Set α) : M.relRank X Y = (M ／ X).eRk Y := rfl

@[simp] lemma relRank_inter_ground_left (M : Matroid α) (X Y : Set α) :
    M.relRank (X ∩ M.E) Y = M.relRank X Y := by
  rw [relRank, contract_inter_ground_eq, relRank]

@[simp] lemma relRank_inter_ground_right (M : Matroid α) (X Y : Set α) :
    M.relRank X (Y ∩ M.E) = M.relRank X Y := by
  rw [relRank, ← eRk_inter_ground, contract_ground, inter_assoc, inter_eq_self_of_subset_right
    diff_subset, ← contract_ground, eRk_inter_ground, relRank]

@[simp] lemma relRank_closure_left (M : Matroid α) (X Y : Set α) :
    M.relRank (M.closure X) Y = M.relRank X Y := by
  rw [relRank, relRank, contract_closure_eq_contract_delete, delete_eRk_eq', LoopEquiv.eRk_eq_eRk]
  rw [loopEquiv_iff_union_eq_union, contract_loops_eq, diff_union_self]

@[simp] lemma relRank_closure_right (M : Matroid α) (X Y : Set α) :
    M.relRank X (M.closure Y) = M.relRank X Y := by
  rw [relRank, relRank, ← eRk_closure_eq _ Y, ← eRk_closure_eq, contract_closure_eq,
    contract_closure_eq, closure_union_closure_left_eq]

lemma relRank_eq_eRk_diff_contract (M : Matroid α) (X Y : Set α) :
    M.relRank X Y = (M ／ X).eRk (Y \ X) := by
  rw [relRank_eq_eRk_contract, ← eRk_closure_eq, contract_closure_eq, eq_comm, ← eRk_closure_eq,
    contract_closure_eq, diff_union_self]

@[simp] lemma relRank_empty_right (M : Matroid α) (X : Set α) : M.relRank X ∅ = 0 := by
  rw [relRank_eq_eRk_contract, eRk_empty]

@[simp] lemma relRank_empty_left (M : Matroid α) (X : Set α) : M.relRank ∅ X = M.eRk X := by
  rw [relRank_eq_eRk_contract, contract_empty]

lemma relRank_eq_diff_right (M : Matroid α) (X Y : Set α) : M.relRank X Y = M.relRank X (Y \ X) :=
  M.relRank_eq_eRk_diff_contract X Y

lemma relRank_eq_union_right (M : Matroid α) (X Y : Set α) :
    M.relRank X Y = M.relRank X (Y ∪ X) := by
  rw [eq_comm, relRank_eq_diff_right, union_diff_right, ← relRank_eq_diff_right]

lemma relRank_eq_zero_of_subset (M : Matroid α) (h : Y ⊆ X) : M.relRank X Y = 0 := by
  rw [relRank_eq_diff_right, diff_eq_empty.2 h, relRank_empty_right]

@[simp] lemma relRank_self (M : Matroid α) (X : Set α) : M.relRank X X = 0 :=
  M.relRank_eq_zero_of_subset rfl.subset

@[simp] lemma relRank_ground_left (M : Matroid α) (X : Set α) : M.relRank M.E X = 0 := by
  rw [← relRank_inter_ground_right, M.relRank_eq_zero_of_subset inter_subset_right]

lemma relRank_eq_relRank_union (M : Matroid α) (X Y : Set α) :
    M.relRank X Y = M.relRank X (Y ∪ X) := by
  rw [relRank, ← eRk_closure_eq, contract_closure_eq, ← relRank_eq_eRk_diff_contract,
    relRank_closure_right]

lemma relRank_le_eRk (M : Matroid α) (X Y : Set α) : M.relRank X Y ≤ M.eRk Y := by
  obtain ⟨I, hI⟩ := (M ／ X).exists_basis (Y ∩ (M ／ X).E)
  rw [relRank, ← eRk_inter_ground, ← hI.encard, ← hI.indep.of_contract.er]
  exact M.eRk_mono (hI.subset.trans inter_subset_left)

lemma relRank_mono_right (M : Matroid α) (X : Set α) {Y Y' : Set α} (hYY' : Y ⊆ Y') :
    M.relRank X Y ≤ M.relRank X Y' :=
  (M ／ X).eRk_mono hYY'

lemma relRank_mono_left (M : Matroid α) {X X' : Set α} (Y : Set α) (h : X ⊆ X') :
    M.relRank X' Y ≤ M.relRank X Y := by
  rw [relRank, relRank, ← union_diff_cancel h, ← contract_contract]
  apply relRank_le_eRk

lemma Basis'.relRank_eq_encard_diff (hI : M.Basis' I (X ∪ C)) (hIC : M.Basis' (I ∩ C) C) :
    M.relRank C X = (I \ C).encard := by
  rw [relRank_eq_relRank_union, relRank, ← eRk_closure_eq, contract_closure_eq, union_assoc,
    union_self, ← hI.closure_eq_closure, ← relRank_eq_eRk_diff_contract, relRank_closure_right,
    relRank_eq_eRk_diff_contract, Indep.er]
  rw [hIC.contract_eq_contract_delete, delete_indep_iff, hIC.indep.contract_indep_iff,
    diff_union_inter, and_iff_left hI.indep, ← disjoint_union_right, union_diff_self,
    union_eq_self_of_subset_left inter_subset_right]
  exact disjoint_sdiff_left

lemma Basis.relRank_eq_encard_diff (hI : M.Basis I (X ∪ C)) (hIC : M.Basis (I ∩ C) C) :
    M.relRank C X = (I \ C).encard :=
  hI.basis'.relRank_eq_encard_diff hIC.basis'

lemma Basis'.relRank_eq_encard_diff_of_subset (hI : M.Basis' I X) (hCX : C ⊆ X)
    (hIC : M.Basis' (I ∩ C) C) : M.relRank C X = (I \ C).encard := by
  rw [← union_eq_self_of_subset_right hCX] at hI
  exact hI.relRank_eq_encard_diff hIC

lemma Basis.relRank_eq_encard_diff_of_subset (hI : M.Basis I X) (hCX : C ⊆ X)
    (hIC : M.Basis (I ∩ C) C) : M.relRank C X = (I \ C).encard :=
  hI.basis'.relRank_eq_encard_diff_of_subset hCX hIC.basis'

lemma Indep.relRank_of_subset (hI : M.Indep I) (hJ : J ⊆ I) : M.relRank J I = (I \ J).encard := by
  rw [hI.basis_self.relRank_eq_encard_diff_of_subset hJ]
  rw [inter_eq_self_of_subset_right hJ]
  exact (hI.subset hJ).basis_self

lemma Basis.relRank_eq_encard_diff_of_subset_basis (hI : M.Basis I X) (hJ : M.Basis J Y)
    (hIJ : I ⊆ J) : M.relRank X Y = (J \ I).encard := by
  rw [← relRank_closure_left, ← hI.closure_eq_closure, relRank_closure_left,
    ← relRank_closure_right, ← hJ.closure_eq_closure,
    relRank_closure_right, hJ.indep.relRank_of_subset hIJ]

lemma relRank_le_eRk_diff (M : Matroid α) (X Y : Set α) : M.relRank X Y ≤ M.eRk (Y \ X) := by
  rw [M.relRank_eq_diff_right]
  apply relRank_le_eRk

lemma relRank_le_encard_diff (M : Matroid α) (X Y : Set α) : M.relRank X Y ≤ (Y \ X).encard :=
  (M.relRank_le_eRk_diff X Y).trans <| M.eRk_le_encard _

lemma relRank_insert_le (M : Matroid α) (X : Set α) (e : α) : M.relRank X (insert e X) ≤ 1 := by
  refine (M.relRank_le_encard_diff X (insert e X)).trans ?_
  rw [encard_le_one_iff]
  aesop

lemma relRank_add_eRk_eq (M : Matroid α) (C X : Set α) :
    M.relRank C X + M.eRk C = M.eRk (X ∪ C) := by
  obtain ⟨I, D, hIC, hD, -, hM⟩ := M.exists_eq_contract_indep_delete C
  obtain ⟨J, hJ, rfl⟩ := hIC.exists_basis_inter_eq_of_superset
    (subset_union_right (s := X ∩ M.E)) (by simp)
  rw [← relRank_inter_ground_left, ← relRank_inter_ground_right,
    hJ.basis'.relRank_eq_encard_diff hIC.basis', ← eRk_inter_ground,
    ← hIC.encard, encard_diff_add_encard_inter, hJ.encard, ← union_inter_distrib_right,
    eRk_inter_ground]

lemma relRank_add_eRk_of_subset (M : Matroid α) (hXY : X ⊆ Y) :
    M.relRank X Y + M.eRk X = M.eRk Y := by
  rw [relRank_add_eRk_eq, union_eq_self_of_subset_right hXY]

lemma rFin.relRank_eq_sub (hY : M.rFin X) (hXY : X ⊆ Y) :
    M.relRank X Y = M.eRk Y - M.eRk X := by
  rw [← relRank_add_eRk_of_subset _ hXY]
  apply WithTop.add_right_cancel <| ne_top_of_lt hY
  rw [eq_comm, tsub_add_cancel_iff_le]
  exact le_add_self

lemma Nonloop.relRank_add_one_eq (he : M.Nonloop e) (X : Set α) :
    M.relRank {e} X + 1 = M.eRk (insert e X) := by
  rw [← union_singleton, ← relRank_add_eRk_eq, he.eRk_eq]

lemma Nonloop.relRank_eq_sub_one (he : M.Nonloop e) (X : Set α) :
    M.relRank {e} X = M.eRk (insert e X) - 1 := by
  apply WithTop.add_right_cancel (show (1 : ℕ∞) ≠ ⊤ from ENat.coe_toNat_eq_self.mp rfl)
  rw [← he.relRank_add_one_eq, eq_comm, tsub_add_cancel_iff_le]
  exact le_add_self

lemma relRank_add_cancel (M : Matroid α) (hXY : X ⊆ Y) (hYZ : Y ⊆ Z) :
    M.relRank X Y + M.relRank Y Z = M.relRank X Z := by
  obtain ⟨I, hI⟩ := M.exists_basis' X
  obtain ⟨J, hJ, hIJ⟩ := hI.indep.subset_basis'_of_subset (hI.subset.trans hXY)
  obtain ⟨K, hK, hJK⟩ := hJ.indep.subset_basis'_of_subset (hJ.subset.trans hYZ)
  obtain rfl := hI.inter_eq_of_subset_indep hIJ hJ.indep
  obtain rfl := hJ.inter_eq_of_subset_indep hJK hK.indep
  rw [hJ.relRank_eq_encard_diff_of_subset hXY hI, hK.relRank_eq_encard_diff_of_subset hYZ hJ,
    hK.relRank_eq_encard_diff_of_subset (hXY.trans hYZ)
    (by rwa [inter_assoc, inter_eq_self_of_subset_right hXY] at hI),
    ← encard_union_eq, diff_eq, diff_eq, inter_assoc, ← inter_union_distrib_left,
    inter_union_distrib_right, union_compl_self, univ_inter, ← compl_inter,
    inter_eq_self_of_subset_left hXY, diff_eq]
  exact disjoint_of_subset_left (diff_subset.trans inter_subset_right)
    disjoint_sdiff_right

lemma relRank_eq_zero_iff (hY : Y ⊆ M.E := by aesop_mat) :
    M.relRank X Y = 0 ↔ Y ⊆ M.closure X := by
  rw [← relRank_closure_left, relRank, eRk_eq_zero_iff', contract_loops_eq, closure_closure,
    diff_self, subset_empty_iff, contract_ground, ← inter_diff_assoc,
    inter_eq_self_of_subset_left hY, diff_eq_empty]

lemma relRank_eq_zero_iff' : M.relRank X Y = 0 ↔ Y ∩ M.E ⊆ M.closure X := by
  rw [← relRank_inter_ground_right, ← relRank_inter_ground_left, relRank_eq_zero_iff,
    closure_inter_ground]

lemma Basis'.relRank_eq_zero (hI : M.Basis' I X) : M.relRank I X = 0 := by
  rw [relRank_eq_zero_iff', hI.closure_eq_closure]
  exact M.inter_ground_subset_closure X

lemma Basis.relRank_eq_zero (hI : M.Basis I X) : M.relRank I X = 0 :=
  hI.basis'.relRank_eq_zero

lemma relRank_insert_eq_zero_iff (he : e ∈ M.E := by aesop_mat) :
    M.relRank X (insert e X) = 0 ↔ e ∈ M.closure X := by
  rw [relRank_eq_zero_iff', insert_inter_of_mem he, insert_subset_iff]
  simp only [and_iff_left_iff_imp]
  exact fun _ ↦ M.inter_ground_subset_closure X

lemma relRank_insert_eq_zero_iff' :
    M.relRank X (insert e X) = 0 ↔ (e ∈ M.E → e ∈ M.closure X) := by
  by_cases he : e ∈ M.E
  · rw [relRank_insert_eq_zero_iff, imp_iff_right he]
  rw [← M.relRank_inter_ground_right, insert_inter_of_not_mem he, relRank_inter_ground_right]
  simp [he]

lemma relRank_ground_eq_zero_iff (hX : X ⊆ M.E := by aesop_mat) :
    M.relRank X M.E = 0 ↔ M.Spanning X := by
  rw [relRank_eq_zero_iff, ground_subset_closure_iff, spanning_iff_closure_eq]

lemma relRank_eq_one_iff (hY : Y ⊆ M.E := by aesop_mat) :
    M.relRank X Y = 1 ↔ ∃ e ∈ Y \ M.closure X, Y ⊆ M.closure (insert e X) := by
  rw [← relRank_closure_left, relRank_eq_eRk_diff_contract, eRk_eq_one_iff
    (show Y \ (M.closure X) ⊆ (M ／ (M.closure X)).E from diff_subset_diff_left hY)]
  simp only [contract_closure_eq, singleton_union, diff_subset_iff, diff_union_self,
    closure_insert_closure_eq_closure_insert, union_diff_self, contract_nonloop_iff,
    closure_closure, union_eq_self_of_subset_left (M.closure_subset_closure (subset_insert _ X))]
  exact ⟨fun ⟨e,he,_,hY'⟩ ↦ ⟨e,he,hY'⟩, fun ⟨e, he, hY'⟩ ↦ ⟨e, he, ⟨hY he.1, he.2⟩, hY'⟩⟩

lemma relRank_le_one_iff (hYne : Y.Nonempty) (hY : Y ⊆ M.E := by aesop_mat) :
    M.relRank X Y ≤ 1 ↔ ∃ e ∈ Y, Y ⊆ M.closure (insert e X) := by
  rw [le_iff_eq_or_lt, lt_iff_not_le, ENat.one_le_iff_ne_zero, not_not, relRank_eq_one_iff,
    relRank_eq_zero_iff]
  refine ⟨?_, fun ⟨e, hY'⟩ ↦ ?_⟩
  · rintro (⟨e, he, hY'⟩ | hY')
    · exact ⟨e, he.1, hY'⟩
    exact ⟨_, hYne.some_mem, hY'.trans (M.closure_subset_closure (subset_insert _ _))⟩
  by_cases he : e ∈ M.closure X
  · rw [← closure_insert_closure_eq_closure_insert, insert_eq_of_mem he, closure_closure] at hY'
    exact Or.inr hY'.2
  exact Or.inl ⟨_, ⟨hY'.1, he⟩, hY'.2⟩

lemma relRank_insert_eq_one (he : e ∈ M.E \ M.closure X) (hX : X ⊆ M.E := by aesop_mat) :
    M.relRank X (insert e X) = 1 := by
  rw [relRank_eq_one_iff]
  exact ⟨e, by simp [he.2], M.subset_closure _ <| insert_subset he.1 hX⟩

lemma relRank_diff_singleton_eq_one_iff (hX : X ⊆ M.E := by aesop_mat) :
    M.relRank (X \ {e}) X = 1 ↔ e ∈ X \ M.closure (X \ {e}) := by
  rw [relRank_eq_one_iff]
  refine ⟨fun ⟨f, hf, hfX⟩ ↦ ?_, fun h ↦ ⟨e, h, ?_⟩⟩
  · have hf' : f ∈ X \ (X \ {e})
    · exact mem_of_mem_of_subset hf (diff_subset_diff_right
        (M.subset_closure _ (diff_subset.trans hX)))
    obtain ⟨-, rfl⟩ : _ ∧ f = e := by simpa using hf'
    assumption
  simp [h.1, M.subset_closure X]

lemma relRank_delete_eq_of_disjoint (M : Matroid α) {D : Set α} (hX : Disjoint X D)
    (hY : Disjoint Y D) : (M ＼ D).relRank X Y = M.relRank X Y := by
  rw [relRank_eq_eRk_contract, ← contract_delete_comm _ hX, delete_eRk_eq _ hY,
    relRank_eq_eRk_contract]

lemma relRank_delete_eq (M : Matroid α) (X Y D : Set α) :
    (M ＼ D).relRank X Y = M.relRank (X \ D) (Y \ D) := by
  rw [← relRank_inter_ground_left, ← relRank_inter_ground_right,
    ← M.relRank_inter_ground_left, ← M.relRank_inter_ground_right,
    relRank_delete_eq_of_disjoint, delete_ground]
  · simp_rw [diff_eq, inter_right_comm, ← inter_assoc]
  · exact disjoint_sdiff_left.mono_left inter_subset_right
  exact disjoint_sdiff_left.mono_left inter_subset_right

lemma relRank_ground_le_iff {k : ℕ} (hX : X ⊆ M.E) :
    M.relRank X M.E ≤ k ↔ ∃ D : Finset α, (D : Set α) ⊆ M.E ∧ D.card ≤ k ∧ M.Spanning (X ∪ D) := by
  obtain ⟨I, hI⟩ := M.exists_basis X
  obtain ⟨B, hB, rfl⟩ := hI.exists_base
  refine ⟨fun h ↦ ?_, fun ⟨D, hD_eq, hDcard, hDsp⟩ ↦ ?_⟩
  · rw [← relRank_closure_left, ← hI.closure_eq_closure, relRank_closure_left, ← hB.closure_eq,
      relRank_closure_right, hB.indep.relRank_of_subset inter_subset_left, diff_self_inter,
      encard_le_cast_iff] at h
    obtain ⟨D, hD_eq, hDcard⟩ := h
    use D
    simp [hD_eq, hDcard, show M.Spanning (X ∪ B) from (hB.spanning.superset subset_union_right),
      show B \ X ⊆ M.E from diff_subset.trans hB.subset_ground]

  rw [← hDsp.closure_eq, relRank_closure_right, union_comm, ← relRank_eq_union_right]
  exact (M.relRank_le_encard_diff X D).trans ((encard_le_card diff_subset).trans <| by simpa)

lemma relRank_union_le_relRank_inter_right (M : Matroid α) (X Y : Set α) :
    M.relRank X (X ∪ Y) ≤ M.relRank (X ∩ Y) Y := by
  wlog hE : X ⊆ M.E ∧ Y ⊆ M.E with aux
  · convert aux _ (X ∩ M.E) (Y ∩ M.E) ⟨inter_subset_right, inter_subset_right⟩ using 1
    · rw [← union_inter_distrib_right, relRank_inter_ground_right, relRank_inter_ground_left]
    rw [← inter_inter_distrib_right, relRank_inter_ground_right, relRank_inter_ground_left]
  obtain ⟨hXE, hYE⟩ := hE
  obtain ⟨I, hI⟩ := M.exists_basis (X ∩ Y)
  obtain ⟨I', hI', rfl⟩ := hI.exists_basis_inter_eq_of_superset inter_subset_left
  obtain ⟨J, hJ, rfl⟩ := hI'.exists_basis_inter_eq_of_superset (Y := X ∪ Y) subset_union_left
  rw [hJ.relRank_eq_encard_diff_of_subset subset_union_left hI']
  rw [inter_comm J, ← inter_inter_distrib_left, ← inter_assoc, inter_comm X, inter_assoc] at hI
  have hi' : M.Indep (J ∩ (X ∩ Y) ∪ (J \ X)) :=
    hJ.indep.subset (union_subset inter_subset_left diff_subset)
  have hJYX : J \ X ⊆ Y := diff_subset_iff.2 hJ.subset
  obtain ⟨K, hKX, hssK⟩ := hi'.subset_basis_of_subset
    (union_subset (inter_subset_right.trans inter_subset_right) hJYX)
  rw [hI.relRank_eq_encard_diff_of_subset_basis hKX (subset_union_left.trans hssK)]
  refine encard_le_card ?_
  rw [union_subset_iff] at hssK
  rw [subset_diff, and_iff_right hssK.2]
  exact disjoint_sdiff_left.mono_right (inter_subset_right.trans inter_subset_left)

lemma relRank_union_le_relRank_inter_left (M : Matroid α) (X Y : Set α) :
    M.relRank Y (X ∪ Y) ≤ M.relRank (X ∩ Y) X := by
  rw [union_comm, inter_comm]
  exact M.relRank_union_le_relRank_inter_right _ _

lemma relRank_union_add_relRank_union_le_relRank_inter_union (X Y : Set α) :
    M.relRank X (X ∪ Y) + M.relRank Y (X ∪ Y) ≤ M.relRank (X ∩ Y) (X ∪ Y) := by
  rw [← ENat.mul_le_mul_left_iff (a := 2) (by simp) (by simp), two_mul, two_mul]
  nth_rewrite 1 [← M.relRank_add_cancel inter_subset_left subset_union_left,
    ← M.relRank_add_cancel inter_subset_right subset_union_right]
  simp_rw [← add_assoc, add_comm (M.relRank (X ∩ Y) _)]
  apply add_le_add_right
  rw [add_assoc, add_assoc]
  refine add_le_add_left (add_le_add ?_ ?_) _
  · apply relRank_union_le_relRank_inter_left
  apply relRank_union_le_relRank_inter_right

-- lemma relRank_le_relRank_left_add_relRank_right (M : Matroid α) {A B : Set α} (hXA : X ⊆ A)
--     (hXB : X ⊆ B) (hAY : A ⊆ Y) (hBY : B ⊆ Y) :
--     M.relRank X Y ≤ M.relRank A Y + M.relRank B Y := by
--   rw [← M.relRank_add_cancel hXA hAY, add_comm]
--   have := M.relRank_union_le_relRank_inter_left





  -- suffices h : 2 * M.relRank (X ∩ Y) (X ∪ Y) ≤ 2 * (M.relRank X (X ∪ Y) + M.relRank Y (X ∪ Y))
  -- ·
  -- rw [← mul_le_mul_iff_right]
  -- refine le_trans (M.relRank_mono_right (Y' := Z ∪ (X ∪ Y)) _ subset_union_left) ?_

  -- wlog hZ : Z = X ∪ Y with aux
  -- · refine le_trans ()


section Contract

lemma eRk_contract_le_eRk_delete (M : Matroid α) (X Y : Set α) : (M ／ X).eRk Y ≤ (M ＼ X).eRk Y := by
  obtain ⟨I, hI⟩ := (M ／ X).exists_basis (Y ∩ (M ／ X).E)
  rw [← eRk_inter_ground, ← hI.encard, ← hI.indep.of_contract.er, delete_eRk_eq']
  refine M.eRk_mono (hI.subset.trans ?_)
  rw [diff_eq, contract_ground, diff_eq, ← inter_assoc]
  exact inter_subset_inter_left _ inter_subset_left

lemma eRk_contract_le_eRk (M : Matroid α) (C X : Set α) : (M ／ C).eRk X ≤ M.eRk X := by
  obtain ⟨I, hI⟩ := (M ／ C).exists_basis (X ∩ (M ／ C).E)
  rw [← eRk_inter_ground, ← hI.encard, ← hI.indep.of_contract.er]
  exact M.eRk_mono (hI.subset.trans inter_subset_left)

lemma eRank_contract_le_eRank_delete (M : Matroid α) (X : Set α) : (M ／ X).eRank ≤ (M ＼ X).eRank := by
  rw [eRank_def, eRank_def]
  exact M.eRk_contract_le_eRk_delete X (M.E \ X)

lemma eRank_contract_le (M : Matroid α) (C : Set α) : (M ／ C).eRank ≤ M.eRank :=
  (M.eRank_contract_le_eRank_delete C).trans (M.eRank_delete_le C)

lemma eRank_contract_add_eRk (M : Matroid α) (C : Set α) : (M ／ C).eRank + M.eRk C = M.eRank := by
  rw [← contract_inter_ground_eq, ← eRk_inter_ground,
    eRank_def, contract_ground, ← relRank_eq_eRk_contract, ← relRank_eq_diff_right, add_comm,
    eRank_def, ← relRank_empty_left, relRank_add_cancel _ (empty_subset _) inter_subset_right,
    relRank_empty_left]

lemma Nonloop.eRank_contract_add_one (M : Matroid α) (he : M.Nonloop e) :
    (M ／ e).eRank + 1 = M.eRank := by
  rw [contract_elem, ← M.eRank_contract_add_eRk {e}, he.eRk_eq]

lemma rFin.contract_rFin (h : M.rFin X) (C : Set α) : (M ／ C).rFin X := by
  rw [← eRk_lt_top_iff] at *; exact (eRk_contract_le_eRk _ _ _).trans_lt h

lemma rFin.union_of_contract (hX : (M ／ C).rFin X) (hC : M.rFin C) : M.rFin (X ∪ C) := by
  rw [← eRk_lt_top_iff, ← M.relRank_add_eRk_eq, relRank]
  rw [← eRk_ne_top_iff] at hC hX
  rw [lt_top_iff_ne_top, Ne, WithTop.add_eq_top, not_or]
  exact ⟨hX, hC⟩

lemma rFin.of_contract (hX : (M ／ C).rFin X) (hC : M.rFin C) : M.rFin X :=
  (hX.union_of_contract hC).subset subset_union_left

lemma rFin.contract_rFin_of_subset_union (h : M.rFin Z) (X C : Set α) (hX : X ⊆ M.closure (Z ∪ C)) :
    (M ／ C).rFin (X \ C) :=
  (h.contract_rFin C).to_closure.subset
    (by rw [contract_closure_eq]; exact diff_subset_diff_left hX)

lemma Minor.eRank_le (h : N ≤m M) : N.eRank ≤ M.eRank := by
  obtain ⟨C, D, -, -, -, rfl⟩ := h
  rw [← eRk_univ_eq, ← eRk_univ_eq, delete_eRk_eq']
  exact (M.eRk_contract_le_eRk _ _).trans (M.eRk_mono diff_subset)

lemma Minor.rk_le (h : N ≤m M) [FiniteRk M] : N.rk ≤ M.rk := by
  have hle := h.eRank_le
  have := h.finiteRk
  rw [← M.coe_rk_eq, ← N.coe_rk_eq] at hle
  exact WithTop.coe_le_coe.1 hle

lemma relRank_contract_le (M : Matroid α) (C X Y : Set α) :
    (M ／ C).relRank X Y ≤ M.relRank X Y := by
  rw [relRank_eq_eRk_contract, relRank_eq_eRk_contract, contract_contract,
    union_comm, ← contract_contract]
  exact (M ／ X).eRk_contract_le_eRk C Y

lemma eRank_contract_eq_relRank_ground (M : Matroid α) (C : Set α) :
    (M ／ C).eRank = M.relRank C M.E := by
  rw [relRank_eq_eRk_contract, eRank_def, contract_ground, ← (M ／ C).eRk_inter_ground M.E,
    contract_ground, inter_eq_self_of_subset_right diff_subset]

end Contract

section Rank

lemma delete_elem_eRank_eq (he : ¬ M.Coloop e) : (M ＼ e).eRank = M.eRank := by
  rw [coloop_iff_diff_nonspanning, not_not] at he
  rw [deleteElem, eRank_def, delete_eRk_eq _ (by simp), delete_ground, ← eRk_closure_eq,
    he.closure_eq, eRank_def]

lemma delete_elem_rk_eq (M : Matroid α) (he : ¬ M.Coloop e) : (M ＼ e).rk = M.rk := by
  rw [rk, delete_elem_eRank_eq he, rk]

lemma delete_r_eq' (M : Matroid α) (D X : Set α) : (M ＼ D).r X = M.r (X \ D) := by
  rw [r, r, delete_eRk_eq']

lemma delete_r_eq_of_disjoint (M : Matroid α) (hDX : Disjoint X D) : (M ＼ D).r X = M.r X := by
  rw [delete_r_eq', hDX.sdiff_eq_left]

lemma delete_elem_r_eq (M : Matroid α) (heX : e ∉ X) : (M ＼ e).r X = M.r X := by
  rw [deleteElem, delete_r_eq', diff_singleton_eq_self heX]

lemma restrict_r_eq' (M : Matroid α) (R X : Set α) : (M ↾ R).r X = M.r (X ∩ R) := by
  rw [r, restrict_eRk_eq', r]

lemma restrict_r_eq (M : Matroid α) {R : Set α} (hXR : X ⊆ R) : (M ↾ R).r X = M.r X := by
  rw [r, M.restrict_eRk_eq hXR, r]

lemma delete_rk_le (M : Matroid α) [M.FiniteRk] (D : Set α) : (M ＼ D).rk ≤ M.rk := by
  rw [rk_def, rk_def, delete_r_eq']
  exact M.r_mono (diff_subset.trans diff_subset)

lemma delete_rk_add_r_ge_rk (M : Matroid α) (D : Set α) : M.rk ≤ (M ＼ D).rk + M.r D := by
  obtain h | h := M.finite_or_infiniteRk
  · rw [rk_def, rk_def, delete_r_eq', delete_ground, diff_diff, union_self]
    refine le_trans ?_ (M.r_union_le_r_add_r (M.E \ D) D)
    simp [M.r_mono subset_union_left]
  obtain ⟨B, hB⟩ := M.exists_base
  rw [rk_def, r, ← eRank_def, ← hB.encard, hB.infinite.encard_eq]
  simp

lemma contract_r_add_eq (M : Matroid α) [FiniteRk M] (C X : Set α) :
    (M ／ C).r X + M.r C = M.r (X ∪ C) := by
  simp_rw [← Nat.cast_inj (R := ℕ∞), Nat.cast_add, cast_r_eq, ← relRank_add_eRk_eq, relRank]

@[simp] lemma contract_r_cast_int_eq (M : Matroid α) [FiniteRk M] (C X : Set α) :
    ((M ／ C).r X : ℤ) = M.r (X ∪ C) - M.r C := by
  rw [← contract_r_add_eq]
  exact eq_sub_of_add_eq rfl

@[simp] lemma contract_rk_cast_int_eq (M : Matroid α) [FiniteRk M] (C : Set α) :
    ((M ／ C).rk : ℤ) = M.rk - M.r C := by
  rw [rk_def, contract_r_cast_int_eq, contract_ground, diff_union_self, ← r_inter_ground,
    inter_eq_self_of_subset_right subset_union_left, rk_def]

lemma Nonloop.contract_r_add_one_eq [FiniteRk M] (he : M.Nonloop e) :
    (M ／ e).r X + 1 = M.r (insert e X) := by
  rw [← union_singleton, ← contract_r_add_eq, he.r_eq, contract_elem]

lemma Nonloop.contract_rk_add_one_eq [FiniteRk M] (he : M.Nonloop e) :
    (M ／ e).rk + 1 = M.rk := by
  rw [rk_def, he.contract_r_add_one_eq, contract_elem, contract_ground, insert_diff_singleton,
    insert_eq_of_mem he.mem_ground, rk_def]

lemma Nonloop.contract_r_cast_int_eq (M : Matroid α) [FiniteRk M] (he : M.Nonloop e) :
    ((M ／ e).r X : ℤ) = M.r (insert e X) - 1 := by
  rw [← he.contract_r_add_one_eq]
  exact eq_sub_of_add_eq rfl

end Rank

section Nullity

lemma Indep.nullity_contract_of_superset (hI : M.Indep I) (hIX : I ⊆ X) :
    (M ／ I).nullity (X \ I) = M.nullity X := by
  obtain ⟨J, hJX, hIJ⟩ := hI.subset_basis'_of_subset hIX
  rw [(hJX.contract_basis'_diff_diff_of_subset hIJ).nullity_eq, hJX.nullity_eq]
  simp [diff_diff_right, diff_diff, union_eq_self_of_subset_left hIJ]

lemma nullity_eq_relRank (M : Matroid α) (X : Set α) (hXE : X ⊆ M.E := by aesop_mat) :
    M.nullity X = M✶.relRank (M.E \ X) M.E := by
  rw [nullity, relRank_eq_eRk_diff_contract, ← delete_compl, delete_dual_eq_dual_contract, eRank_def]
  simp

lemma nullity_dual_eq (M : Matroid α) (X : Set α) (hXE : X ⊆ M.E := by aesop_mat) :
    M✶.nullity X = M.relRank (M.E \ X) M.E := by
  rw [M✶.nullity_eq_relRank _ hXE, dual_dual, dual_ground]

lemma nullity_compl_dual_eq (M : Matroid α) (X : Set α) :
    M✶.nullity (M.E \ X) = M.relRank X M.E := by
  rw [← relRank_inter_ground_left, M.nullity_dual_eq _ diff_subset, sdiff_sdiff_right_self,
    inter_comm]
  rfl

lemma nullity_delete (M : Matroid α) (hXD : Disjoint X D) : (M ＼ D).nullity X = M.nullity X := by
  rw [delete_eq_restrict, M.nullity_eq_nullity_inter_ground_add_encard_diff,
    nullity_eq_nullity_inter_ground_add_encard_diff, restrict_ground_eq,
    nullity_restrict_of_subset _ inter_subset_right, inter_diff_distrib_left,
    diff_diff_right, hXD.inter_eq, diff_empty, union_empty]

lemma nullity_delete_le (M : Matroid α) (X D : Set α) : (M ＼ D).nullity (X \ D) ≤ M.nullity X := by
  obtain ⟨I, hI⟩ := (M ＼ D).exists_basis' (X \ D)
  have hI' := hI
  rw [← restrict_compl, basis'_restrict_iff, diff_inter_diff_right, subset_diff] at hI'

  obtain ⟨J, hJX, hIJ⟩ := hI'.1.indep.subset_basis'_of_subset
    (hI'.1.subset.trans (diff_subset.trans inter_subset_left))

  obtain rfl : I = J \ D := hI.eq_of_subset_indep
    (by simp [hJX.indep.subset diff_subset, disjoint_sdiff_left])
    (subset_diff.2 ⟨hIJ, hI'.2.2⟩) (diff_subset_diff_left hJX.subset)

  rw [hI.nullity_eq, hJX.nullity_eq, diff_diff, union_diff_self]
  exact encard_le_card (diff_subset_diff_right subset_union_right)

lemma nullity_contract_le (M : Matroid α) (hCX : C ⊆ X) :
    (M ／ C).nullity (X \ C) ≤ M.nullity X := by
  rw [nullity_eq_eRank_restrict_dual, nullity_eq_eRank_restrict_dual,
    contract_restrict_eq_restrict_contract _ _ _ disjoint_sdiff_right, diff_union_self,
    union_eq_self_of_subset_right hCX, contract_dual_eq_dual_delete]
  apply eRank_delete_le

lemma nullity_contract_ge_of_disjoint (M : Matroid α) (hXC : Disjoint X C) :
    M.nullity X ≤ (M ／ C).nullity X := by
  have hle := (M ↾ (X ∪ C))✶.eRank_contract_le_eRank_delete C
  rw [nullity_eq_eRank_restrict_dual, nullity_eq_eRank_restrict_dual,
    contract_restrict_eq_restrict_contract _ _ _ hXC.symm, contract_dual_eq_dual_delete]
  rwa [← delete_dual_eq_dual_contract, delete_eq_restrict, restrict_ground_eq,
    restrict_restrict_eq _ diff_subset, union_diff_cancel_right (Set.disjoint_iff.mp hXC)] at hle

end Nullity
