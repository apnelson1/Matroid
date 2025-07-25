import Matroid.Minor.Order
import Matroid.Rank.Nat
import Matroid.Rank.Nullity
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

@[simp] lemma delete_isRkFinite_iff : (M ＼ D).IsRkFinite X ↔ M.IsRkFinite (X \ D) := by
  rw [← eRk_lt_top_iff, delete_eRk_eq', eRk_lt_top_iff]

lemma Coindep.delete_eRank_eq (hX : M.Coindep X) : (M ＼ X).eRank = M.eRank := by
  rw [coindep_iff_closure_compl_eq_ground] at hX
  rw [eRank_def, delete_ground, delete_eRk_eq', diff_diff, union_self, ← eRk_closure_eq, hX,
    eRank_def]

lemma eRank_delete_le (M : Matroid α) (D : Set α) : (M ＼ D).eRank ≤ M.eRank := by
  rw [eRank_def, delete_ground, delete_eRk_eq', diff_diff, union_self, eRank_def]
  exact M.eRk_mono diff_subset

lemma Indep.delete_eRank_dual_eq (hI : M.Indep I) : (M ／ I)✶.eRank = M✶.eRank := by
  rw [← hI.coindep.delete_eRank_eq, dual_contract]

lemma Indep.eRank_dual_restrict_eq (hI : M.Indep I) : (M ↾ I)✶.eRank = 0 := by
  simp [hI.restrict_eq_freeOn]

lemma IsBasis.eRank_dual_restrict_of_disjoint (hB : M.IsBasis I (I ∪ X)) (hdj : Disjoint I X) :
    (M ↾ (I ∪ X))✶.eRank = X.encard := by
  rw [← IsBase.encard_compl_eq hB.restrict_isBase]
  simp [hdj.sdiff_eq_right]

lemma IsBasis.eRank_dual_restrict (hB : M.IsBasis I X) : (M ↾ X)✶.eRank = (X \ I).encard := by
  rw [← IsBase.encard_compl_eq hB.restrict_isBase, restrict_ground_eq]

@[simp] lemma eRank_dual_restrict_eq_zero_iff : (M ↾ I)✶.eRank = 0 ↔ M.Indep I := by
  rw [← restrict_eq_freeOn_iff, eRank_eq_zero_iff, dual_ground, restrict_ground_eq,
    eq_comm, eq_dual_comm, loopyOn_dual_eq]

lemma Indep.contract_eRk_dual_eq (hI : M.Indep I) : (M ／ I)✶.eRank = M✶.eRank := by
  rw [dual_contract, hI.coindep.delete_eRank_eq]

end Delete

lemma eRank_project (M : Matroid α) (C : Set α) : (M.project C).eRank = (M ／ C).eRank := by
  obtain ⟨B, hB⟩ := (M.project C).exists_isBase
  rw [← hB.encard_eq_eRank, IsBase.encard_eq_eRank (B := B)]
  rwa [← project_isBase_eq]

lemma eRk_project_eq_eRk_contract (M : Matroid α) (C X : Set α) :
    (M.project C).eRk X = (M ／ C).eRk X := by
  rw [project, eRk_restrict, ← eRk_inter_ground, inter_assoc, contract_ground,
    inter_eq_self_of_subset_right diff_subset, ← contract_ground, eRk_inter_ground]

lemma eRk_project_eq (M : Matroid α) (C : Set α) : (M.project C).eRk = (M ／ C).eRk := by
  ext; apply eRk_project_eq_eRk_contract

/-- The relative `ℕ∞`-rank of sets `X` and `Y`, defined to be the `ℕ∞`-rank of `Y` in `M ／ X`,
and equal to the minimum number of elements that need to be added to `X` to span `Y`.
The definition suggests that `X` and `Y` should be disjoint, but it is also a natural
expression when `X ⊆ Y`, and sometimes more generally. -/
noncomputable def eRelRk (M : Matroid α) (X Y : Set α) : ℕ∞ := (M ／ X).eRk Y

lemma eRelRk_eq_eRk_contract (M : Matroid α) (X Y : Set α) : M.eRelRk X Y = (M ／ X).eRk Y := rfl

lemma eRelRk_eq_eRk_project (M : Matroid α) (X Y : Set α) : M.eRelRk X Y = (M.project X).eRk Y := by
  rw [eRk_project_eq_eRk_contract, eRelRk_eq_eRk_contract]

@[simp] lemma eRelRk_inter_ground_left (M : Matroid α) (X Y : Set α) :
    M.eRelRk (X ∩ M.E) Y = M.eRelRk X Y := by
  rw [eRelRk, contract_inter_ground_eq, eRelRk]

@[simp] lemma eRelRk_inter_ground_right (M : Matroid α) (X Y : Set α) :
    M.eRelRk X (Y ∩ M.E) = M.eRelRk X Y := by
  rw [eRelRk, ← eRk_inter_ground, contract_ground, inter_assoc, inter_eq_self_of_subset_right
    diff_subset, ← contract_ground, eRk_inter_ground, eRelRk]

@[simp] lemma eRelRk_closure_left (M : Matroid α) (X Y : Set α) :
    M.eRelRk (M.closure X) Y = M.eRelRk X Y := by
  rw [eRelRk, eRelRk, contract_closure_eq_contract_delete, delete_eRk_eq', IsLoopEquiv.eRk_eq_eRk]
  rw [isLoopEquiv_iff_union_eq_union, contract_loops_eq, diff_union_self]

@[simp] lemma eRelRk_closure_right (M : Matroid α) (X Y : Set α) :
    M.eRelRk X (M.closure Y) = M.eRelRk X Y := by
  rw [eRelRk, eRelRk, ← eRk_closure_eq _ Y, ← eRk_closure_eq, contract_closure_eq,
    contract_closure_eq, closure_union_closure_left_eq]

lemma eRelRk_eq_eRk_diff_contract (M : Matroid α) (X Y : Set α) :
    M.eRelRk X Y = (M ／ X).eRk (Y \ X) := by
  rw [eRelRk_eq_eRk_contract, ← eRk_closure_eq, contract_closure_eq, eq_comm, ← eRk_closure_eq,
    contract_closure_eq, diff_union_self]

@[simp] lemma eRelRk_empty_right (M : Matroid α) (X : Set α) : M.eRelRk X ∅ = 0 := by
  rw [eRelRk_eq_eRk_contract, eRk_empty]

@[simp] lemma eRelRk_empty_left (M : Matroid α) (X : Set α) : M.eRelRk ∅ X = M.eRk X := by
  rw [eRelRk_eq_eRk_contract, contract_empty]

lemma eRelRk_eq_diff_right (M : Matroid α) (X Y : Set α) : M.eRelRk X Y = M.eRelRk X (Y \ X) :=
  M.eRelRk_eq_eRk_diff_contract X Y

lemma eRelRk_eq_union_right (M : Matroid α) (X Y : Set α) : M.eRelRk X Y = M.eRelRk X (Y ∪ X) := by
  rw [eq_comm, eRelRk_eq_diff_right, union_diff_right, ← eRelRk_eq_diff_right]

lemma eRelRk_eq_zero_of_subset (M : Matroid α) (h : Y ⊆ X) : M.eRelRk X Y = 0 := by
  rw [eRelRk_eq_diff_right, diff_eq_empty.2 h, eRelRk_empty_right]

@[simp] lemma eRelRk_self (M : Matroid α) (X : Set α) : M.eRelRk X X = 0 :=
  M.eRelRk_eq_zero_of_subset rfl.subset

@[simp] lemma eRelRk_ground_left (M : Matroid α) (X : Set α) : M.eRelRk M.E X = 0 := by
  rw [← eRelRk_inter_ground_right, M.eRelRk_eq_zero_of_subset inter_subset_right]

lemma eRelRk_eq_eRelRk_union (M : Matroid α) (X Y : Set α) : M.eRelRk X Y = M.eRelRk X (Y ∪ X) := by
  rw [eRelRk, ← eRk_closure_eq, contract_closure_eq, ← eRelRk_eq_eRk_diff_contract,
    eRelRk_closure_right]

lemma eRelRk_le_eRk (M : Matroid α) (X Y : Set α) : M.eRelRk X Y ≤ M.eRk Y := by
  obtain ⟨I, hI⟩ := (M ／ X).exists_isBasis (Y ∩ (M ／ X).E)
  rw [eRelRk, ← eRk_inter_ground, ← hI.encard_eq_eRk, ← hI.indep.of_contract.eRk_eq_encard]
  exact M.eRk_mono (hI.subset.trans inter_subset_left)

lemma eRelRk_mono_right (M : Matroid α) (X : Set α) {Y Y' : Set α} (hYY' : Y ⊆ Y') :
    M.eRelRk X Y ≤ M.eRelRk X Y' :=
  (M ／ X).eRk_mono hYY'

lemma eRelRk_mono_left (M : Matroid α) {X X' : Set α} (Y : Set α) (h : X ⊆ X') :
    M.eRelRk X' Y ≤ M.eRelRk X Y := by
  rw [eRelRk, eRelRk, ← union_diff_cancel h, ← contract_contract]
  apply eRelRk_le_eRk

/-- If `Y` contains a basis `I` for `X`, then `M.eRelRk X Y` is the number of elements that need
to be added to `I` to give a basis for `Y`. -/
lemma IsBasis'.eRelRk_eq_encard_of_union_isBasis_disjoint (hI : M.IsBasis' I X)
    (hIJ : M.IsBasis' (I ∪ J) Y) (hdj : Disjoint I J) : M.eRelRk X Y = J.encard := by
  rw [← eRelRk_closure_right, ← hIJ.closure_eq_closure, eRelRk_closure_right,
    ← eRelRk_closure_left, ← hI.closure_eq_closure, eRelRk_closure_left,
    eRelRk_eq_eRk_diff_contract, union_diff_cancel_left (hdj.inter_eq.subset), Indep.eRk_eq_encard]
  rwa [hI.indep.contract_indep_iff, union_comm, disjoint_comm, and_iff_left hIJ.indep]

/-- If `I` is a basis for `X ∪ C` containing a basis for `C`, then the relative rank of
`C` and `X` is the size of `I \ C`. -/
lemma IsBasis'.eRelRk_eq_encard_diff (hI : M.IsBasis' I (X ∪ C)) (hIC : M.IsBasis' (I ∩ C) C) :
    M.eRelRk C X = (I \ C).encard := by
  rw [eRelRk_eq_union_right, hIC.eRelRk_eq_encard_of_union_isBasis_disjoint (J := I \ C) (by simpa)
    disjoint_sdiff_inter.symm]

lemma IsBasis.eRelRk_eq_encard_diff (hI : M.IsBasis I (X ∪ C)) (hIC : M.IsBasis (I ∩ C) C) :
    M.eRelRk C X = (I \ C).encard :=
  hI.isBasis'.eRelRk_eq_encard_diff hIC.isBasis'

lemma IsBasis'.eRelRk_eq_encard_diff_of_subset (hI : M.IsBasis' I X) (hCX : C ⊆ X)
    (hIC : M.IsBasis' (I ∩ C) C) : M.eRelRk C X = (I \ C).encard := by
  rw [← union_eq_self_of_subset_right hCX] at hI
  exact hI.eRelRk_eq_encard_diff hIC

lemma IsBasis.eRelRk_eq_encard_diff_of_subset (hI : M.IsBasis I X) (hCX : C ⊆ X)
    (hIC : M.IsBasis (I ∩ C) C) : M.eRelRk C X = (I \ C).encard :=
  hI.isBasis'.eRelRk_eq_encard_diff_of_subset hCX hIC.isBasis'

lemma Indep.eRelRk_of_subset (hI : M.Indep I) (hJ : J ⊆ I) : M.eRelRk J I = (I \ J).encard := by
  rw [hI.isBasis_self.eRelRk_eq_encard_diff_of_subset hJ]
  rw [inter_eq_self_of_subset_right hJ]
  exact (hI.subset hJ).isBasis_self

lemma IsBasis.eRelRk_eq_encard_diff_of_subset_isBasis (hI : M.IsBasis I X) (hJ : M.IsBasis J Y)
    (hIJ : I ⊆ J) : M.eRelRk X Y = (J \ I).encard := by
  rw [← eRelRk_closure_left, ← hI.closure_eq_closure, eRelRk_closure_left,
    ← eRelRk_closure_right, ← hJ.closure_eq_closure,
    eRelRk_closure_right, hJ.indep.eRelRk_of_subset hIJ]

lemma eRelRk_le_eRk_diff (M : Matroid α) (X Y : Set α) : M.eRelRk X Y ≤ M.eRk (Y \ X) := by
  rw [M.eRelRk_eq_diff_right]
  apply eRelRk_le_eRk

lemma eRelRk_le_encard_diff (M : Matroid α) (X Y : Set α) : M.eRelRk X Y ≤ (Y \ X).encard :=
  (M.eRelRk_le_eRk_diff X Y).trans <| M.eRk_le_encard _

lemma eRelRk_insert_le (M : Matroid α) (X : Set α) (e : α) : M.eRelRk X (insert e X) ≤ 1 := by
  refine (M.eRelRk_le_encard_diff X (insert e X)).trans ?_
  rw [encard_le_one_iff]
  aesop

lemma eRelRk_add_eRk_of_subset (M : Matroid α) (hXY : X ⊆ Y) :
    M.eRelRk X Y + M.eRk X = M.eRk Y := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  obtain ⟨J, hJ, rfl⟩ := hI.exists_isBasis'_inter_eq_of_superset hXY
  rw [hJ.eRelRk_eq_encard_diff_of_subset hXY hI, ← hI.encard_eq_eRk, encard_diff_add_encard_inter,
    hJ.encard_eq_eRk]

lemma eRelRk_add_eRk_eq (M : Matroid α) (C X : Set α) : M.eRelRk C X + M.eRk C = M.eRk (X ∪ C) := by
  rw [eRelRk_eq_eRelRk_union, eRelRk_add_eRk_of_subset]
  exact subset_union_right

lemma IsRkFinite.eRelRk_eq_sub (hY : M.IsRkFinite X) (hXY : X ⊆ Y) :
    M.eRelRk X Y = M.eRk Y - M.eRk X := by
  rw [← eRelRk_add_eRk_of_subset _ hXY]
  apply WithTop.add_right_cancel <| ne_top_of_lt hY.eRk_lt_top
  rw [eq_comm, tsub_add_cancel_iff_le]
  exact le_add_self

lemma IsNonloop.eRelRk_add_one_eq (he : M.IsNonloop e) (X : Set α) :
    M.eRelRk {e} X + 1 = M.eRk (insert e X) := by
  rw [← union_singleton, ← eRelRk_add_eRk_eq, he.eRk_eq]

lemma IsNonloop.eRelRk_eq_sub_one (he : M.IsNonloop e) (X : Set α) :
    M.eRelRk {e} X = M.eRk (insert e X) - 1 := by
  apply WithTop.add_right_cancel (show (1 : ℕ∞) ≠ ⊤ from ENat.coe_toNat_eq_self.mp rfl)
  rw [← he.eRelRk_add_one_eq, eq_comm, tsub_add_cancel_iff_le]
  exact le_add_self

lemma eRelRk_add_cancel (M : Matroid α) (hXY : X ⊆ Y) (hYZ : Y ⊆ Z) :
    M.eRelRk X Y + M.eRelRk Y Z = M.eRelRk X Z := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  obtain ⟨J, hJ, rfl⟩ := hI.exists_isBasis'_inter_eq_of_superset hXY
  obtain ⟨J, hK, rfl⟩ := hJ.exists_isBasis'_inter_eq_of_superset hYZ
  rw [hJ.eRelRk_eq_encard_diff_of_subset hXY hI, hK.eRelRk_eq_encard_diff_of_subset hYZ hJ,
    hK.eRelRk_eq_encard_diff_of_subset (hXY.trans hYZ), ← encard_union_eq (by tauto_set),
    union_comm, ← diff_self_inter, diff_union_diff_cancel' (by tauto_set) (by tauto_set)]
  rwa [inter_assoc, inter_eq_self_of_subset_right hXY] at hI

lemma eRelRk_eq_zero_iff (hY : Y ⊆ M.E := by aesop_mat) :
    M.eRelRk X Y = 0 ↔ Y ⊆ M.closure X := by
  rw [← eRelRk_closure_left, eRelRk, eRk_eq_zero_iff', contract_loops_eq, closure_closure,
    diff_self, subset_empty_iff, contract_ground, ← inter_diff_assoc,
    inter_eq_self_of_subset_left hY, diff_eq_empty]

lemma eRelRk_eq_zero_iff' : M.eRelRk X Y = 0 ↔ Y ∩ M.E ⊆ M.closure X := by
  rw [← eRelRk_inter_ground_right, ← eRelRk_inter_ground_left, eRelRk_eq_zero_iff,
    closure_inter_ground]

lemma IsBasis'.eRelRk_eq_zero (hI : M.IsBasis' I X) : M.eRelRk I X = 0 := by
  rw [eRelRk_eq_zero_iff', hI.closure_eq_closure]
  exact M.inter_ground_subset_closure X

lemma IsBasis.eRelRk_eq_zero (hI : M.IsBasis I X) : M.eRelRk I X = 0 :=
  hI.isBasis'.eRelRk_eq_zero

lemma eRelRk_insert_eq_zero_iff (he : e ∈ M.E := by aesop_mat) :
    M.eRelRk X (insert e X) = 0 ↔ e ∈ M.closure X := by
  rw [eRelRk_eq_zero_iff', insert_inter_of_mem he, insert_subset_iff]
  simp only [and_iff_left_iff_imp]
  exact fun _ ↦ M.inter_ground_subset_closure X

lemma eRelRk_insert_eq_zero_iff' : M.eRelRk X (insert e X) = 0 ↔ (e ∈ M.E → e ∈ M.closure X) := by
  by_cases he : e ∈ M.E
  · rw [eRelRk_insert_eq_zero_iff, imp_iff_right he]
  rw [← M.eRelRk_inter_ground_right, insert_inter_of_notMem he, eRelRk_inter_ground_right]
  simp [he]

lemma eRelRk_ground_eq_zero_iff (hX : X ⊆ M.E := by aesop_mat) :
    M.eRelRk X M.E = 0 ↔ M.Spanning X := by
  rw [eRelRk_eq_zero_iff, ground_subset_closure_iff, spanning_iff_closure_eq]

lemma eRelRk_eq_one_iff (hY : Y ⊆ M.E := by aesop_mat) :
    M.eRelRk X Y = 1 ↔ ∃ e ∈ Y \ M.closure X, Y ⊆ M.closure (insert e X) := by
  rw [← eRelRk_closure_left, eRelRk_eq_eRk_diff_contract, eRk_eq_one_iff
    (show Y \ (M.closure X) ⊆ (M ／ (M.closure X)).E from diff_subset_diff_left hY)]
  simp only [contract_closure_eq, singleton_union, diff_subset_iff,
    closure_insert_closure_eq_closure_insert, union_diff_self, contract_isNonloop_iff,
    closure_closure, union_eq_self_of_subset_left (M.closure_subset_closure (subset_insert _ X))]
  exact ⟨fun ⟨e,he,_,hY'⟩ ↦ ⟨e,he,hY'⟩, fun ⟨e, he, hY'⟩ ↦ ⟨e, he, ⟨hY he.1, he.2⟩, hY'⟩⟩

lemma eRelRk_le_one_iff (hYne : Y.Nonempty) (hY : Y ⊆ M.E := by aesop_mat) :
    M.eRelRk X Y ≤ 1 ↔ ∃ e ∈ Y, Y ⊆ M.closure (insert e X) := by
  rw [le_iff_eq_or_lt, lt_iff_not_ge, ENat.one_le_iff_ne_zero, not_not, eRelRk_eq_one_iff,
    eRelRk_eq_zero_iff]
  refine ⟨?_, fun ⟨e, hY'⟩ ↦ ?_⟩
  · rintro (⟨e, he, hY'⟩ | hY')
    · exact ⟨e, he.1, hY'⟩
    exact ⟨_, hYne.some_mem, hY'.trans (M.closure_subset_closure (subset_insert _ _))⟩
  by_cases he : e ∈ M.closure X
  · rw [← closure_insert_closure_eq_closure_insert, insert_eq_of_mem he, closure_closure] at hY'
    exact Or.inr hY'.2
  exact Or.inl ⟨_, ⟨hY'.1, he⟩, hY'.2⟩

lemma eRelRk_insert_eq_one (he : e ∈ M.E \ M.closure X) (hX : X ⊆ M.E := by aesop_mat) :
    M.eRelRk X (insert e X) = 1 := by
  rw [eRelRk_eq_one_iff]
  exact ⟨e, by simp [he.2], M.subset_closure _ <| insert_subset he.1 hX⟩

lemma eRelRk_diff_singleton_eq_one_iff (hX : X ⊆ M.E := by aesop_mat) :
    M.eRelRk (X \ {e}) X = 1 ↔ e ∈ X \ M.closure (X \ {e}) := by
  rw [eRelRk_eq_one_iff]
  refine ⟨fun ⟨f, hf, hfX⟩ ↦ ?_, fun h ↦ ⟨e, h, ?_⟩⟩
  · have hf' : f ∈ X \ (X \ {e})
    · exact mem_of_mem_of_subset hf (diff_subset_diff_right
        (M.subset_closure _ (diff_subset.trans hX)))
    obtain ⟨-, rfl⟩ : _ ∧ f = e := by simpa using hf'
    assumption
  simp [h.1, M.subset_closure X]

lemma eRelRk_delete_eq_of_disjoint (M : Matroid α) {D : Set α} (hX : Disjoint X D)
    (hY : Disjoint Y D) : (M ＼ D).eRelRk X Y = M.eRelRk X Y := by
  rw [eRelRk_eq_eRk_contract, ← contract_delete_comm _ hX, delete_eRk_eq _ hY,
    eRelRk_eq_eRk_contract]

lemma eRelRk_delete_eq (M : Matroid α) (X Y D : Set α) :
    (M ＼ D).eRelRk X Y = M.eRelRk (X \ D) (Y \ D) := by
  rw [← eRelRk_inter_ground_left, ← eRelRk_inter_ground_right,
    ← M.eRelRk_inter_ground_left, ← M.eRelRk_inter_ground_right,
    eRelRk_delete_eq_of_disjoint, delete_ground]
  · simp_rw [diff_eq, inter_right_comm, ← inter_assoc]
  · exact disjoint_sdiff_left.mono_left inter_subset_right
  exact disjoint_sdiff_left.mono_left inter_subset_right

lemma eRelRk_ground_le_iff {k : ℕ} (hX : X ⊆ M.E) :
    M.eRelRk X M.E ≤ k ↔ ∃ D : Finset α, (D : Set α) ⊆ M.E ∧ D.card ≤ k ∧ M.Spanning (X ∪ D) := by
  obtain ⟨I, hI⟩ := M.exists_isBasis X
  obtain ⟨B, hB, rfl⟩ := hI.exists_isBase
  refine ⟨fun h ↦ ?_, fun ⟨D, hD_eq, hDcard, hDsp⟩ ↦ ?_⟩
  · rw [← eRelRk_closure_left, ← hI.closure_eq_closure, eRelRk_closure_left, ← hB.closure_eq,
      eRelRk_closure_right, hB.indep.eRelRk_of_subset inter_subset_left, diff_self_inter,
      encard_le_cast_iff] at h
    obtain ⟨D, hD_eq, hDcard⟩ := h
    use D
    simp [hD_eq, hDcard, show M.Spanning (X ∪ B) from (hB.spanning.superset subset_union_right),
      show B \ X ⊆ M.E from diff_subset.trans hB.subset_ground]
  rw [← hDsp.closure_eq, eRelRk_closure_right, union_comm, ← eRelRk_eq_union_right]
  exact (M.eRelRk_le_encard_diff X D).trans ((encard_le_encard diff_subset).trans <| by simpa)

lemma eRelRk_union_le_eRelRk_inter_right (M : Matroid α) (X Y : Set α) :
    M.eRelRk X (X ∪ Y) ≤ M.eRelRk (X ∩ Y) Y := by
  wlog hE : X ⊆ M.E ∧ Y ⊆ M.E with aux
  · convert aux _ (X ∩ M.E) (Y ∩ M.E) ⟨inter_subset_right, inter_subset_right⟩ using 1
    · rw [← union_inter_distrib_right, eRelRk_inter_ground_right, eRelRk_inter_ground_left]
    rw [← inter_inter_distrib_right, eRelRk_inter_ground_right, eRelRk_inter_ground_left]
  obtain ⟨hXE, hYE⟩ := hE
  obtain ⟨I, hI⟩ := M.exists_isBasis (X ∩ Y)
  obtain ⟨I', hI', rfl⟩ := hI.exists_isBasis_inter_eq_of_superset inter_subset_left
  obtain ⟨J, hJ, rfl⟩ := hI'.exists_isBasis_inter_eq_of_superset (Y := X ∪ Y) subset_union_left
  rw [hJ.eRelRk_eq_encard_diff_of_subset subset_union_left hI']
  rw [inter_comm J, ← inter_inter_distrib_left, ← inter_assoc, inter_comm X, inter_assoc] at hI
  have hi' : M.Indep (J ∩ (X ∩ Y) ∪ (J \ X)) :=
    hJ.indep.subset (union_subset inter_subset_left diff_subset)
  have hJYX : J \ X ⊆ Y := diff_subset_iff.2 hJ.subset
  obtain ⟨K, hKX, hssK⟩ := hi'.subset_isBasis_of_subset
    (union_subset (inter_subset_right.trans inter_subset_right) hJYX)
  rw [hI.eRelRk_eq_encard_diff_of_subset_isBasis hKX (subset_union_left.trans hssK)]
  refine encard_le_encard ?_
  rw [union_subset_iff] at hssK
  rw [subset_diff, and_iff_right hssK.2]
  exact disjoint_sdiff_left.mono_right (inter_subset_right.trans inter_subset_left)

lemma eRelRk_union_le_eRelRk_inter_left (M : Matroid α) (X Y : Set α) :
    M.eRelRk Y (X ∪ Y) ≤ M.eRelRk (X ∩ Y) X := by
  rw [union_comm, inter_comm]
  exact M.eRelRk_union_le_eRelRk_inter_right _ _

lemma eRelRk_union_add_eRelRk_union_le_eRelRk_inter_union (X Y : Set α) :
    M.eRelRk X (X ∪ Y) + M.eRelRk Y (X ∪ Y) ≤ M.eRelRk (X ∩ Y) (X ∪ Y) := by
  rw [← ENat.mul_le_mul_left_iff (a := 2) (by simp) (by simp), two_mul, two_mul]
  nth_rewrite 1 [← M.eRelRk_add_cancel inter_subset_left subset_union_left,
    ← M.eRelRk_add_cancel inter_subset_right subset_union_right]
  simp_rw [← add_assoc, add_comm (M.eRelRk (X ∩ Y) _)]
  apply add_le_add_right
  rw [add_assoc, add_assoc]
  refine add_le_add_left (add_le_add ?_ ?_) _
  · apply eRelRk_union_le_eRelRk_inter_left
  apply eRelRk_union_le_eRelRk_inter_right

-- lemma eRelRk_le_eRelRk_left_add_eRelRk_right (M : Matroid α) {A B : Set α} (hXA : X ⊆ A)
--     (hXB : X ⊆ B) (hAY : A ⊆ Y) (hBY : B ⊆ Y) :
--     M.eRelRk X Y ≤ M.eRelRk A Y + M.eRelRk B Y := by
--   rw [← M.eRelRk_add_cancel hXA hAY, add_comm]
--   have := M.eRelRk_union_le_eRelRk_inter_left





  -- suffices h : 2 * M.eRelRk (X ∩ Y) (X ∪ Y) ≤ 2 * (M.eRelRk X (X ∪ Y) + M.eRelRk Y (X ∪ Y))
  -- ·
  -- rw [← mul_le_mul_iff_right]
  -- refine le_trans (M.eRelRk_mono_right (Y' := Z ∪ (X ∪ Y)) _ subset_union_left) ?_

  -- wlog hZ : Z = X ∪ Y with aux
  -- · refine le_trans ()


section Contract

lemma eRk_contract_le_eRk_delete (M : Matroid α) (X Y : Set α) :
    (M ／ X).eRk Y ≤ (M ＼ X).eRk Y := by
  obtain ⟨I, hI⟩ := (M ／ X).exists_isBasis (Y ∩ (M ／ X).E)
  rw [← eRk_inter_ground, ← hI.encard_eq_eRk, ← hI.indep.of_contract.eRk_eq_encard, delete_eRk_eq']
  refine M.eRk_mono (hI.subset.trans ?_)
  rw [diff_eq, contract_ground, diff_eq, ← inter_assoc]
  exact inter_subset_inter_left _ inter_subset_left

lemma eRk_contract_le_eRk (M : Matroid α) (C X : Set α) : (M ／ C).eRk X ≤ M.eRk X := by
  obtain ⟨I, hI⟩ := (M ／ C).exists_isBasis (X ∩ (M ／ C).E)
  rw [← eRk_inter_ground, ← hI.encard_eq_eRk, ← hI.indep.of_contract.eRk_eq_encard]
  exact M.eRk_mono (hI.subset.trans inter_subset_left)

lemma eRank_contract_le_eRank_delete (M : Matroid α) (X : Set α) :
    (M ／ X).eRank ≤ (M ＼ X).eRank := by
  rw [eRank_def, eRank_def]
  exact M.eRk_contract_le_eRk_delete X (M.E \ X)

lemma eRank_contract_le (M : Matroid α) (C : Set α) : (M ／ C).eRank ≤ M.eRank :=
  (M.eRank_contract_le_eRank_delete C).trans (M.eRank_delete_le C)

lemma eRank_contract_add_eRk (M : Matroid α) (C : Set α) : (M ／ C).eRank + M.eRk C = M.eRank := by
  rw [← contract_inter_ground_eq, ← eRk_inter_ground,
    eRank_def, contract_ground, ← eRelRk_eq_eRk_contract, ← eRelRk_eq_diff_right, add_comm,
    eRank_def, ← eRelRk_empty_left, eRelRk_add_cancel _ (empty_subset _) inter_subset_right,
    eRelRk_empty_left]

lemma IsNonloop.eRank_contractElem_add_one (M : Matroid α) (he : M.IsNonloop e) :
    (M ／ {e}).eRank + 1 = M.eRank := by
  rw [← M.eRank_contract_add_eRk {e}, he.eRk_eq]

lemma IsRkFinite.contract_isRkFinite (h : M.IsRkFinite X) (C : Set α) : (M ／ C).IsRkFinite X := by
  rw [← eRk_lt_top_iff] at *
  exact (eRk_contract_le_eRk _ _ _).trans_lt h

lemma IsRkFinite.union_of_contract (hX : (M ／ C).IsRkFinite X) (hC : M.IsRkFinite C) :
    M.IsRkFinite (X ∪ C) := by
  rw [← eRk_lt_top_iff, ← M.eRelRk_add_eRk_eq, eRelRk]
  rw [← eRk_ne_top_iff] at hC hX
  rw [lt_top_iff_ne_top, Ne, WithTop.add_eq_top, not_or]
  exact ⟨hX, hC⟩

lemma IsRkFinite.of_contract (hX : (M ／ C).IsRkFinite X) (hC : M.IsRkFinite C) : M.IsRkFinite X :=
  (hX.union_of_contract hC).subset subset_union_left

lemma IsRkFinite.contract_isRkFinite_of_subset_union (h : M.IsRkFinite Z) (X C : Set α)
    (hX : X ⊆ M.closure (Z ∪ C)) : (M ／ C).IsRkFinite (X \ C) :=
  (h.contract_isRkFinite C).closure.subset
    (by rw [contract_closure_eq]; exact diff_subset_diff_left hX)

lemma IsMinor.eRank_le (h : N ≤m M) : N.eRank ≤ M.eRank := by
  obtain ⟨C, D, -, -, -, rfl⟩ := h
  rw [← eRk_univ_eq, ← eRk_univ_eq, delete_eRk_eq']
  exact (M.eRk_contract_le_eRk _ _).trans (M.eRk_mono diff_subset)

lemma IsMinor.rank_le (h : N ≤m M) [RankFinite M] : N.rank ≤ M.rank := by
  have hle := h.eRank_le
  have := h.rankFinite
  rw [← M.cast_rank_eq, ← N.cast_rank_eq] at hle
  exact WithTop.coe_le_coe.1 hle

lemma eRelRk_contract_le (M : Matroid α) (C X Y : Set α) :
    (M ／ C).eRelRk X Y ≤ M.eRelRk X Y := by
  rw [eRelRk_eq_eRk_contract, eRelRk_eq_eRk_contract, contract_contract,
    union_comm, ← contract_contract]
  exact (M ／ X).eRk_contract_le_eRk C Y

lemma eRank_contract_eq_eRelRk_ground (M : Matroid α) (C : Set α) :
    (M ／ C).eRank = M.eRelRk C M.E := by
  rw [eRelRk_eq_eRk_contract, eRank_def, contract_ground, ← (M ／ C).eRk_inter_ground M.E,
    contract_ground, inter_eq_self_of_subset_right diff_subset]

end Contract

section Rank

lemma deleteElem_eRank_eq (he : ¬ M.IsColoop e) : (M ＼ {e}).eRank = M.eRank := by
  rw [isColoop_iff_diff_not_spanning, not_not] at he
  rw [eRank_def, delete_eRk_eq _ (by simp), delete_ground, ← eRk_closure_eq, he.closure_eq,
    eRank_def]

lemma delete_elem_rank_eq (M : Matroid α) (he : ¬ M.IsColoop e) : (M ＼ {e}).rank = M.rank := by
  rw [rank, deleteElem_eRank_eq he, rank]

lemma delete_rk_eq' (M : Matroid α) (D X : Set α) : (M ＼ D).rk X = M.rk (X \ D) := by
  rw [rk, rk, delete_eRk_eq']

lemma delete_rk_eq_of_disjoint (M : Matroid α) (hDX : Disjoint X D) : (M ＼ D).rk X = M.rk X := by
  rw [delete_rk_eq', hDX.sdiff_eq_left]

lemma deleteElem_rk_eq (M : Matroid α) (heX : e ∉ X) : (M ＼ {e}).rk X = M.rk X := by
  rw [delete_rk_eq', diff_singleton_eq_self heX]

lemma restrict_rk_eq' (M : Matroid α) (R X : Set α) : (M ↾ R).rk X = M.rk (X ∩ R) := by
  rw [rk, restrict_eRk_eq', rk]

lemma restrict_rk_eq (M : Matroid α) {R : Set α} (hXR : X ⊆ R) : (M ↾ R).rk X = M.rk X := by
  rw [rk, M.restrict_eRk_eq hXR, rk]

lemma delete_rank_le (M : Matroid α) [M.RankFinite] (D : Set α) : (M ＼ D).rank ≤ M.rank := by
  rw [rank_def, rank_def, delete_rk_eq']
  exact M.rk_mono (diff_subset.trans diff_subset)

lemma delete_eRank_add_eRk_ge_eRank (M : Matroid α) (D : Set α) :
    M.eRank ≤ (M ＼ D).eRank + M.eRk D := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [← eRk_ground, ← eRk_ground, delete_eRk_eq _ (by simpa using disjoint_sdiff_left),
    delete_ground]
  exact le_trans (by simp) <| M.eRk_union_le_eRk_add_eRk (M.E \ D) D

lemma delete_rank_add_rk_ge_rank (M : Matroid α) (D : Set α) : M.rank ≤ (M ＼ D).rank + M.rk D := by
  obtain h | h := M.rankFinite_or_rankInfinite
  · rw [rank_def, rank_def, delete_rk_eq', delete_ground, diff_diff, union_self]
    refine le_trans ?_ (M.rk_union_le_rk_add_rk (M.E \ D) D)
    simp
  obtain ⟨B, hB⟩ := M.exists_isBase
  rw [rank_def, rk, ← eRank_def, ← hB.encard_eq_eRank, hB.infinite.encard_eq]
  simp

lemma contract_rk_add_eq (M : Matroid α) [RankFinite M] (C X : Set α) :
    (M ／ C).rk X + M.rk C = M.rk (X ∪ C) := by
  simp_rw [← Nat.cast_inj (R := ℕ∞), Nat.cast_add, cast_rk_eq, ← eRelRk_add_eRk_eq, eRelRk]

@[simp] lemma contract_rk_cast_int_eq (M : Matroid α) [RankFinite M] (C X : Set α) :
    ((M ／ C).rk X : ℤ) = M.rk (X ∪ C) - M.rk C := by
  rw [← contract_rk_add_eq]
  exact eq_sub_of_add_eq rfl

@[simp] lemma contract_rank_cast_int_eq (M : Matroid α) [RankFinite M] (C : Set α) :
    ((M ／ C).rank : ℤ) = M.rank - M.rk C := by
  rw [rank_def, contract_rk_cast_int_eq, contract_ground, diff_union_self, ← rk_inter_ground,
    inter_eq_self_of_subset_right subset_union_left, rank_def]

lemma IsNonloop.contractElem_rk_add_one_eq [RankFinite M] (he : M.IsNonloop e) :
    (M ／ {e}).rk X + 1 = M.rk (insert e X) := by
  rw [← union_singleton, ← contract_rk_add_eq, he.rk_eq]

lemma IsNonloop.contractElem_rank_add_one_eq [RankFinite M] (he : M.IsNonloop e) :
    (M ／ {e}).rank + 1 = M.rank := by
  rw [rank_def, he.contractElem_rk_add_one_eq, contract_ground, insert_diff_singleton,
    insert_eq_of_mem he.mem_ground, rank_def]

lemma IsNonloop.contractElem_rk_intCast_eq (M : Matroid α) [RankFinite M] (he : M.IsNonloop e) :
    ((M ／ {e}).rk X : ℤ) = M.rk (insert e X) - 1 := by
  rw [← he.contractElem_rk_add_one_eq]
  exact eq_sub_of_add_eq rfl

/-- Move to `minor`-/
lemma RankFinite.ofDelete {D : Set α} (hD : M.IsRkFinite D) (hfin : (M ＼ D).RankFinite) :
    M.RankFinite := by
  rw [← eRank_ne_top_iff, ← lt_top_iff_ne_top]
  refine (M.delete_eRank_add_eRk_ge_eRank D).trans_lt ?_
  simpa [ENat.add_lt_top, eRk_lt_top_iff, hD]


end Rank

section Nullity

lemma Indep.nullity_contract_of_superset (hI : M.Indep I) (hIX : I ⊆ X) :
    (M ／ I).nullity (X \ I) = M.nullity X := by
  obtain ⟨J, hJX, hIJ⟩ := hI.subset_isBasis'_of_subset hIX
  rw [(hJX.contract_isBasis'_diff_diff_of_subset hIJ).nullity_eq, hJX.nullity_eq]
  simp [diff_diff_right, diff_diff, union_eq_self_of_subset_left hIJ]

lemma nullity_eq_eRelRk (M : Matroid α) (X : Set α) (hXE : X ⊆ M.E := by aesop_mat) :
    M.nullity X = M✶.eRelRk (M.E \ X) M.E := by
  rw [nullity, eRelRk_eq_eRk_diff_contract, ← delete_compl, dual_delete, eRank_def]
  simp

lemma nullity_dual_eq (M : Matroid α) (X : Set α) (hXE : X ⊆ M.E := by aesop_mat) :
    M✶.nullity X = M.eRelRk (M.E \ X) M.E := by
  rw [M✶.nullity_eq_eRelRk _ hXE, dual_dual, dual_ground]

lemma nullity_compl_dual_eq (M : Matroid α) (X : Set α) :
    M✶.nullity (M.E \ X) = M.eRelRk X M.E := by
  rw [← eRelRk_inter_ground_left, M.nullity_dual_eq _ diff_subset, sdiff_sdiff_right_self,
    inter_comm]
  rfl

lemma nullity_delete (M : Matroid α) (hXD : Disjoint X D) : (M ＼ D).nullity X = M.nullity X := by
  rw [nullity_eq_eRank_restrict_dual, nullity_eq_eRank_restrict_dual,
    delete_restrict_eq_restrict _ hXD.symm]

lemma nullity_delete_le (M : Matroid α) (X D : Set α) : (M ＼ D).nullity (X \ D) ≤ M.nullity X := by
  rw [nullity_eq_eRank_restrict_dual, nullity_eq_eRank_restrict_dual, delete_restrict_eq_restrict
    _ disjoint_sdiff_right]
  exact (dual_isMinor_iff.2 (IsRestriction.of_subset M diff_subset).isMinor).eRank_le

lemma nullity_contract_le (M : Matroid α) (hCX : C ⊆ X) :
    (M ／ C).nullity (X \ C) ≤ M.nullity X := by
  rw [nullity_eq_eRank_restrict_dual, nullity_eq_eRank_restrict_dual,
    contract_restrict_eq_restrict_contract _ disjoint_sdiff_right, diff_union_self,
    union_eq_self_of_subset_right hCX, dual_contract]
  apply eRank_delete_le

lemma nullity_contract_ge_of_disjoint (M : Matroid α) (hXC : Disjoint X C) :
    M.nullity X ≤ (M ／ C).nullity X := by
  have hle := (M ↾ (X ∪ C))✶.eRank_contract_le_eRank_delete C
  rw [nullity_eq_eRank_restrict_dual, nullity_eq_eRank_restrict_dual,
    contract_restrict_eq_restrict_contract _ hXC.symm, dual_contract]
  rwa [← dual_delete, delete_eq_restrict, restrict_ground_eq,
    restrict_restrict_eq _ diff_subset, union_diff_cancel_right (Set.disjoint_iff.mp hXC)] at hle

end Nullity

section relRk

/-- `M.relRk X Y` is the relative rank of `X` and `Y` as a natural number.
If `M.eRelRk X Y` is infinite, this has the junk value of zero.
If `Y` has finite rank and `X ⊆ Y`, then this is the difference between the ranks of `X` and `Y`. -/
noncomputable def relRk (X Y : Set α) : ℕ := (M.eRelRk X Y).toNat

lemma relRk_intCast_eq_sub (M : Matroid α) [RankFinite M] (X Y : Set α) :
    (M.relRk X Y : ℤ) = M.rk (X ∪ Y) - M.rk X := by
  rw [relRk, eRelRk_eq_union_right, (M.isRkFinite_set X).eRelRk_eq_sub subset_union_right,
    ENat.toNat_sub (M.isRkFinite_set X).eRk_lt_top.ne, ← rk, ← rk, Nat.cast_sub , union_comm]
  exact (M.rk_mono (subset_union_right))

lemma relRk_intCast_eq_sub_of_subset (M : Matroid α) [RankFinite M] (hXY : X ⊆ Y) :
    (M.relRk X Y : ℤ) = M.rk Y - M.rk X := by
  rw [relRk_intCast_eq_sub, union_eq_self_of_subset_left hXY]

end relRk
