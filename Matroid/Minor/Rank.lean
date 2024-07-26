import Matroid.Minor.Basic

open Set

namespace Matroid

variable {α : Type*} {M N : Matroid α} {I J C D X Y Z : Set α} {e f : α}

section Delete

@[simp] lemma delete_er_eq' (M : Matroid α) (D X : Set α) : (M ＼ D).er X = M.er (X \ D) := by
  rw [← restrict_compl, restrict_er_eq', diff_eq, inter_comm M.E, ← inter_assoc, ← diff_eq,
    er_inter_ground_eq]

lemma delete_er_eq (M : Matroid α) (h : Disjoint X D) : (M ＼ D).er X = M.er X := by
  rwa [delete_er_eq', sdiff_eq_left.2]

lemma delete_er_eq_delete_er_diff (M : Matroid α) (D X : Set α) :
    (M ＼ D).er X = (M ＼ D).er (X \ D) := by
  simp

@[simp] lemma delete_rFin_iff : (M ＼ D).rFin X ↔ M.rFin (X \ D) := by
  rw [← er_lt_top_iff, delete_er_eq', er_lt_top_iff]

lemma Coindep.delete_erk_eq (hX : M.Coindep X) : (M ＼ X).erk = M.erk := by
  rw [coindep_iff_closure_compl_eq_ground] at hX
  rw [erk_eq_er_ground, delete_ground, delete_er_eq', diff_diff, union_self, ← er_closure_eq, hX,
    erk_eq_er_ground]

lemma Indep.delete_erk_dual_eq (hI : M.Indep I) : (M ／ I)✶.erk = M✶.erk := by
  rw [← hI.coindep.delete_erk_eq, contract_dual_eq_dual_delete]

lemma Indep.erk_dual_restrict_eq (hI : M.Indep I) : (M ↾ I)✶.erk = 0 := by
  simp [hI.restrict_eq_freeOn]

lemma Basis.erk_dual_restrict_of_disjoint (hB : M.Basis I (I ∪ X)) (hdj : Disjoint I X) :
    (M ↾ (I ∪ X))✶.erk = X.encard := by
  rw [← Base.encard_compl_eq hB.restrict_base]; simp [hdj.sdiff_eq_right]

lemma Basis.erk_dual_restrict (hB : M.Basis I X) : (M ↾ X)✶.erk = (X \ I).encard := by
  rw [← Base.encard_compl_eq hB.restrict_base, restrict_ground_eq]

@[simp] lemma erk_dual_restrict_eq_zero_iff : (M ↾ I)✶.erk = 0 ↔ M.Indep I := by
  rw [← restrict_eq_freeOn_iff, erk_eq_zero_iff, dual_ground, restrict_ground_eq,
    eq_comm, eq_dual_comm, loopyOn_dual_eq]

lemma Indep.contract_er_dual_eq (hI : M.Indep I) : (M ／ I)✶.erk = M✶.erk := by
  rw [contract_dual_eq_dual_delete, hI.coindep.delete_erk_eq]

end Delete

/-- The relative rank of sets `X` and `Y`, defined to be the rank of `Y` in `M ／ X`,
and equal to the minimum number of elements that need to be added to `X` to span `Y`.
The definition suggests that `X` and `Y` should be disjoint, but it is also a natural
expression when `X ⊆ Y`, and sometimes more generally. -/
noncomputable def relRank (M : Matroid α) (X Y : Set α) : ℕ∞ := (M ／ X).er Y

lemma relRank_eq_er_contract (M : Matroid α) (X Y : Set α) : M.relRank X Y = (M ／ X).er Y := rfl

lemma relRank_le_er (M : Matroid α) (X Y : Set α) : M.relRank X Y ≤ M.er Y := by
  obtain ⟨I, hI⟩ := (M ／ X).exists_basis (Y ∩ (M ／ X).E)
  rw [relRank, ← er_inter_ground_eq, ← hI.encard, ← hI.indep.of_contract.er]
  exact M.er_mono (hI.subset.trans inter_subset_left)

lemma relRank_eq_er_diff_contract (M : Matroid α) (X Y : Set α) :
    M.relRank X Y = (M ／ X).er (Y \ X) := by
  rw [relRank_eq_er_contract, ← er_closure_eq, contract_closure_eq, eq_comm, ← er_closure_eq,
    contract_closure_eq, diff_union_self]

lemma relRank_eq_diff_right (M : Matroid α) (X Y : Set α) : M.relRank X Y = M.relRank X (Y \ X) :=
  M.relRank_eq_er_diff_contract X Y

lemma relRank_eq_union_right (M : Matroid α) (X Y : Set α) :
    M.relRank X Y = M.relRank X (Y ∪ X) := by
  rw [eq_comm, relRank_eq_diff_right, union_diff_right, ← relRank_eq_diff_right]

lemma relRank_mono_right (M : Matroid α) (X : Set α) {Y Y' : Set α} (hYY' : Y ⊆ Y') :
    M.relRank X Y ≤ M.relRank X Y' :=
  (M ／ X).er_mono hYY'

lemma relRank_mono_left (M : Matroid α) {X X' : Set α} (Y : Set α) (h : X ⊆ X') :
    M.relRank X' Y ≤ M.relRank X Y := by
  rw [relRank, relRank, ← union_diff_cancel h, ← contract_contract]
  apply relRank_le_er

@[simp] lemma relRank_empty_right (M : Matroid α) (X : Set α) : M.relRank X ∅ = 0 := by
  rw [relRank_eq_er_contract, er_empty]

@[simp] lemma relRank_empty_left (M : Matroid α) (X : Set α) : M.relRank ∅ X = M.er X := by
  rw [relRank_eq_er_contract, contract_empty]

lemma relRank_eq_zero_of_subset (M : Matroid α) (h : Y ⊆ X) : M.relRank X Y = 0 := by
  rw [relRank_eq_diff_right, diff_eq_empty.2 h, relRank_empty_right]

@[simp] lemma relRank_closure_left (M : Matroid α) (X Y : Set α) :
    M.relRank (M.closure X) Y = M.relRank X Y := by
  rw [relRank, relRank, contract_closure_eq_contract_delete, delete_er_eq', LoopEquiv.er_eq_er]
  rw [loopEquiv_iff_union_eq_union, contract_loops_eq, diff_union_self]

@[simp] lemma relRank_closure_right (M : Matroid α) (X Y : Set α) :
    M.relRank X (M.closure Y) = M.relRank X Y := by
  refine le_antisymm ?_ ?_
  · rw [relRank_eq_er_diff_contract,  relRank, ← (M ／ X).er_closure_eq Y, contract_closure_eq]
    exact (M ／ X).er_mono (diff_subset_diff_left (M.closure_subset_closure subset_union_left))
  rw [relRank, ← er_inter_ground_eq, contract_ground, ← inter_diff_assoc]
  exact er_mono _ <| diff_subset.trans
    ((M.subset_closure _).trans (M.closure_subset_closure inter_subset_left))

@[simp] lemma relRank_inter_ground_left (M : Matroid α) (X Y : Set α) :
    M.relRank (X ∩ M.E) Y = M.relRank X Y := by
  rw [←relRank_closure_left, closure_inter_ground, relRank_closure_left]

@[simp] lemma relRank_inter_ground_right (M : Matroid α) (X Y : Set α) :
    M.relRank X (Y ∩ M.E) = M.relRank X Y := by
  rw [← relRank_closure_right, eq_comm, ← relRank_closure_right, closure_inter_ground]

@[simp] lemma relRank_ground_left (M : Matroid α) (X : Set α) : M.relRank M.E X = 0 := by
  rw [← relRank_inter_ground_right, M.relRank_eq_zero_of_subset inter_subset_right]

lemma relRank_eq_relRank_union (M : Matroid α) (X Y : Set α) :
    M.relRank X Y = M.relRank X (Y ∪ X) := by
  rw [relRank, ← er_closure_eq, contract_closure_eq, ← relRank_eq_er_diff_contract,
    relRank_closure_right]

lemma Basis'.relRank_eq_encard_diff (hI : M.Basis' I (X ∪ C)) (hIC : M.Basis' (I ∩ C) C) :
    M.relRank C X = (I \ C).encard := by
  rw [relRank_eq_relRank_union, relRank, ← er_closure_eq, contract_closure_eq, union_assoc,
    union_self, ← hI.closure_eq_closure, ← relRank_eq_er_diff_contract, relRank_closure_right,
    relRank_eq_er_diff_contract, Indep.er]
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

lemma relRank_le_er_diff (M : Matroid α) (X Y : Set α) : M.relRank X Y ≤ M.er (Y \ X) := by
  rw [M.relRank_eq_diff_right]
  apply relRank_le_er

lemma relRank_le_encard_diff (M : Matroid α) (X Y : Set α) : M.relRank X Y ≤ (Y \ X).encard :=
  (M.relRank_le_er_diff X Y).trans <| M.er_le_encard _

lemma relRank_insert_le (M : Matroid α) (X : Set α) (e : α) : M.relRank X (insert e X) ≤ 1 := by
  refine (M.relRank_le_encard_diff X (insert e X)).trans ?_
  rw [encard_le_one_iff]
  aesop

lemma relRank_add_er_eq (M : Matroid α) (C X : Set α) :
    M.relRank C X + M.er C = M.er (X ∪ C) := by
  obtain ⟨I, D, hIC, hD, -, hM⟩ := M.exists_eq_contract_indep_delete C
  obtain ⟨J, hJ, rfl⟩ := hIC.exists_basis_inter_eq_of_superset
    (subset_union_right (s := X ∩ M.E)) (by simp)
  rw [← relRank_inter_ground_left, ← relRank_inter_ground_right,
    hJ.basis'.relRank_eq_encard_diff hIC.basis', ← er_inter_ground_eq,
    ← hIC.encard, encard_diff_add_encard_inter, hJ.encard, ← union_inter_distrib_right,
    er_inter_ground_eq]

lemma relRank_add_er_of_subset (M : Matroid α) (hXY : X ⊆ Y) :
    M.relRank X Y + M.er X = M.er Y := by
  rw [relRank_add_er_eq, union_eq_self_of_subset_right hXY]

lemma rFin.relRank_eq_sub (hY : M.rFin X) (hXY : X ⊆ Y) :
    M.relRank X Y = M.er Y - M.er X := by
  rw [← relRank_add_er_of_subset _ hXY]
  apply WithTop.add_right_cancel <| ne_top_of_lt hY
  rw [eq_comm, tsub_add_cancel_iff_le]
  exact le_add_self

lemma Nonloop.relRank_add_one_eq (he : M.Nonloop e) (X : Set α) :
    M.relRank {e} X + 1 = M.er (insert e X) := by
  rw [← union_singleton, ← relRank_add_er_eq, he.er_eq]

lemma Nonloop.relRank_eq_sub_one (he : M.Nonloop e) (X : Set α) :
    M.relRank {e} X = M.er (insert e X) - 1 := by
  apply WithTop.add_right_cancel (show (1 : ℕ∞) ≠ ⊤ from ENat.coe_toNat_eq_self.mp rfl)
  rw [← he.relRank_add_one_eq, eq_comm, tsub_add_cancel_iff_le]
  exact le_add_self

lemma relRank_add_of_subset_of_subset (M : Matroid α) (hXY : X ⊆ Y) (hYZ : Y ⊆ Z) :
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
  rw [← relRank_closure_left, relRank, er_eq_zero_iff', contract_loops_eq, closure_closure,
    diff_self, subset_empty_iff, contract_ground, ← inter_diff_assoc,
    inter_eq_self_of_subset_left hY, diff_eq_empty]

lemma relRank_eq_zero_iff' : M.relRank X Y = 0 ↔ Y ∩ M.E ⊆ M.closure X := by
  rw [← relRank_inter_ground_right, ← relRank_inter_ground_left, relRank_eq_zero_iff,
    closure_inter_ground]

lemma relRank_eq_one_iff (hY : Y ⊆ M.E := by aesop_mat) :
    M.relRank X Y = 1 ↔ ∃ e ∈ Y \ M.closure X, Y ⊆ M.closure (insert e X) := by
  rw [← relRank_closure_left, relRank_eq_er_diff_contract, er_eq_one_iff
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


section Contract

lemma er_contract_le_er (M : Matroid α) (C X : Set α) : (M ／ C).er X ≤ M.er X :=
  by
  obtain ⟨I, hI⟩ := (M ／ C).exists_basis (X ∩ (M ／ C).E)
  rw [← er_inter_ground_eq, ← hI.encard, ← hI.indep.of_contract.er]
  exact M.er_mono (hI.subset.trans inter_subset_left)

lemma rFin.contract_rFin (h : M.rFin X) (C : Set α) : (M ／ C).rFin X := by
  rw [← er_lt_top_iff] at *; exact (er_contract_le_er _ _ _).trans_lt h

lemma rFin.union_of_contract (hX : (M ／ C).rFin X) (hC : M.rFin C) : M.rFin (X ∪ C) := by
  rw [← er_lt_top_iff, ← M.relRank_add_er_eq, relRank]
  rw [← er_ne_top_iff] at hC hX
  rw [lt_top_iff_ne_top, Ne, WithTop.add_eq_top, not_or]
  exact ⟨hX, hC⟩

lemma rFin.of_contract (hX : (M ／ C).rFin X) (hC : M.rFin C) : M.rFin X :=
  (hX.union_of_contract hC).subset subset_union_left

lemma rFin.contract_rFin_of_subset_union (h : M.rFin Z) (X C : Set α) (hX : X ⊆ M.closure (Z ∪ C)) :
    (M ／ C).rFin (X \ C) :=
  (h.contract_rFin C).to_closure.subset
    (by rw [contract_closure_eq]; exact diff_subset_diff_left hX)

lemma Minor.erk_le (h : N ≤m M) : N.erk ≤ M.erk := by
  obtain ⟨C, D, -, -, -, rfl⟩ := h
  rw [← er_univ_eq, ← er_univ_eq, delete_er_eq']
  exact (M.er_contract_le_er _ _).trans (M.er_mono diff_subset)

lemma Minor.rk_le (h : N ≤m M) [FiniteRk M] : N.rk ≤ M.rk := by
  have hle := h.erk_le
  have := h.finiteRk
  rw [← M.coe_rk_eq, ← N.coe_rk_eq] at hle
  exact WithTop.coe_le_coe.1 hle

end Contract

section Rank

lemma delete_r_eq' (M : Matroid α) (D X : Set α) : (M ＼ D).r X = M.r (X \ D) := by
  rw [r, r, delete_er_eq']

lemma delete_r_eq_of_disjoint (M : Matroid α) (hDX : Disjoint X D) : (M ＼ D).r X = M.r X := by
  rw [delete_r_eq', hDX.sdiff_eq_left]

lemma delete_elem_r_eq (M : Matroid α) (heX : e ∉ X) : (M ＼ e).r X = M.r X := by
  rw [deleteElem, delete_r_eq', diff_singleton_eq_self heX]

lemma restrict_r_eq' (M : Matroid α) (R X : Set α) : (M ↾ R).r X = M.r (X ∩ R) := by
  rw [r, restrict_er_eq', r]

lemma restrict_r_eq (M : Matroid α) {R : Set α} (hXR : X ⊆ R) : (M ↾ R).r X = M.r X := by
  rw [r, M.restrict_er_eq hXR, r]

lemma contract_r_add_eq (M : Matroid α) [FiniteRk M] (C X : Set α) :
    (M ／ C).r X + M.r C = M.r (X ∪ C) := by
  simp_rw [← Nat.cast_inj (R := ℕ∞), Nat.cast_add, coe_r_eq, ← relRank_add_er_eq, relRank]

@[simp] lemma contract_r_cast_int_Eq (M : Matroid α) [FiniteRk M] (C X : Set α) :
    ((M ／ C).r X : ℤ) = M.r (X ∪ C) - M.r C := by
  rw [← contract_r_add_eq]
  exact eq_sub_of_add_eq rfl

lemma Nonloop.contract_r_add_one_eq (M : Matroid α) [FiniteRk M] (he : M.Nonloop e) :
    (M ／ e).r X + 1 = M.r (insert e X) := by
  rw [← union_singleton, ← contract_r_add_eq, he.r_eq, contract_elem]

lemma Nonloop.contract_r_cast_int_eq (M : Matroid α) [FiniteRk M] (he : M.Nonloop e) :
    ((M ／ e).r X : ℤ) = M.r (insert e X) - 1 := by
  rw [← he.contract_r_add_one_eq]
  exact eq_sub_of_add_eq rfl

end Rank
