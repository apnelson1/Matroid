import Matroid.Rank.Nat
import Matroid.ForMathlib.Set

open Set

variable {α : Type*} {M M' N : Matroid α} {e f : α} {I J R B X Y Z K S : Set α}

namespace Matroid

section Delete

variable {D D₁ D₂ R : Set α}

class HasDelete (α β : Type*) where
  del : α → β → α

infixl:75 " ＼ " => HasDelete.del

/-- The deletion `M ＼ D` is the restriction of a matroid `M` to `M.E \ D`-/
def delete (M : Matroid α) (D : Set α) : Matroid α :=
  M ↾ (M.E \ D)

instance delSet {α : Type*} : HasDelete (Matroid α) (Set α) :=
  ⟨Matroid.delete⟩

lemma delete_eq_restrict (M : Matroid α) (D : Set α) : M ＼ D = M ↾ (M.E \ D) := rfl

/-- Can this be an abbrev? -/
instance delElem {α : Type*} : HasDelete (Matroid α) α :=
  ⟨fun M e ↦ M.delete {e}⟩

instance delete_finite [M.Finite] : (M ＼ D).Finite :=
  ⟨M.ground_finite.diff⟩

instance deleteElem_finite [Matroid.Finite M] : (M ＼ e).Finite :=
  delete_finite

instance delete_finiteRk [FiniteRk M] : FiniteRk (M ＼ D) :=
  restrict_finiteRk _

lemma restrict_compl (M : Matroid α) (D : Set α) : M ↾ (M.E \ D) = M ＼ D := rfl

@[simp] lemma delete_compl (hR : R ⊆ M.E := by aesop_mat) : M ＼ (M.E \ R) = M ↾ R := by
  rw [← restrict_compl, diff_diff_cancel_left hR]

@[simp] lemma delete_restriction (M : Matroid α) (D : Set α) : M ＼ D ≤r M :=
  restrict_restriction _ _ diff_subset

lemma Restriction.exists_eq_delete (hNM : N ≤r M) : ∃ D ⊆ M.E, N = M ＼ D :=
  ⟨M.E \ N.E, diff_subset, by obtain ⟨R, hR, rfl⟩ := hNM; rw [delete_compl, restrict_ground_eq]⟩

lemma restriction_iff_exists_eq_delete : N ≤r M ↔ ∃ D ⊆ M.E, N = M ＼ D :=
  ⟨Restriction.exists_eq_delete, by rintro ⟨D, -, rfl⟩; apply delete_restriction⟩

@[simp] lemma delete_ground (M : Matroid α) (D : Set α) : (M ＼ D).E = M.E \ D := rfl

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma delete_subset_ground (M : Matroid α) (D : Set α) : (M ＼ D).E ⊆ M.E :=
  diff_subset

@[simp] lemma deleteElem (M : Matroid α) (e : α) : M ＼ e = M ＼ ({e} : Set α) := rfl

lemma deleteElem_eq_self (he : e ∉ M.E) : M ＼ e = M := by
  rwa [deleteElem, delete_eq_restrict, restrict_eq_self_iff, sdiff_eq_left,
    disjoint_singleton_right]

instance deleteElem_finiteRk [FiniteRk M] {e : α} : FiniteRk (M ＼ e) := by
  rw [deleteElem]; infer_instance

@[simp] lemma delete_delete (M : Matroid α) (D₁ D₂ : Set α) : M ＼ D₁ ＼ D₂ = M ＼ (D₁ ∪ D₂) := by
  rw [← restrict_compl, ← restrict_compl, ← restrict_compl, restrict_restrict_eq,
    restrict_ground_eq, diff_diff]
  simp [diff_subset]

lemma delete_comm (M : Matroid α) (D₁ D₂ : Set α) : M ＼ D₁ ＼ D₂ = M ＼ D₂ ＼ D₁ := by
  rw [delete_delete, union_comm, delete_delete]

lemma delete_inter_ground_eq (M : Matroid α) (D : Set α) : M ＼ (D ∩ M.E) = M ＼ D := by
  rw [← restrict_compl, ← restrict_compl, diff_inter_self_eq_diff]

lemma delete_eq_delete_iff : M ＼ D₁ = M ＼ D₂ ↔ D₁ ∩ M.E = D₂ ∩ M.E := by
  rw [← delete_inter_ground_eq, ← M.delete_inter_ground_eq D₂]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h]⟩
  apply_fun (M.E \ Matroid.E ·) at h
  simp_rw [delete_ground, diff_diff_cancel_left inter_subset_right] at h
  assumption

@[simp] lemma delete_eq_self_iff : M ＼ D = M ↔ Disjoint D M.E := by
  rw [← restrict_compl, restrict_eq_self_iff, sdiff_eq_left, disjoint_comm]

lemma Restriction.restrict_delete_of_disjoint (h : N ≤r M) (hX : Disjoint X N.E) :
    N ≤r (M ＼ X) := by
  obtain ⟨D, hD, rfl⟩ := restriction_iff_exists_eq_delete.1 h
  refine restriction_iff_exists_eq_delete.2 ⟨D \ X, diff_subset_diff_left hD, ?_⟩
  rwa [delete_delete, union_diff_self, union_comm, ← delete_delete, eq_comm,
    delete_eq_self_iff]

lemma Restriction.restriction_deleteElem (h : N ≤r M) (he : e ∉ N.E) : N ≤r M ＼ e :=
  h.restrict_delete_of_disjoint (by simpa)

@[simp] lemma delete_indep_iff : (M ＼ D).Indep I ↔ M.Indep I ∧ Disjoint I D := by
  rw [← restrict_compl, restrict_indep_iff, subset_diff, ← and_assoc,
    and_iff_left_of_imp Indep.subset_ground]

@[simp] lemma deleteElem_indep_iff : (M ＼ e).Indep I ↔ M.Indep I ∧ e ∉ I := by
  rw [deleteElem, delete_indep_iff, disjoint_singleton_right]

lemma Indep.of_delete (h : (M ＼ D).Indep I) : M.Indep I :=
  (delete_indep_iff.mp h).1

lemma Indep.indep_delete_of_disjoint (h : M.Indep I) (hID : Disjoint I D) : (M ＼ D).Indep I :=
  delete_indep_iff.mpr ⟨h, hID⟩

lemma indep_iff_delete_of_disjoint (hID : Disjoint I D) : M.Indep I ↔ (M ＼ D).Indep I :=
  ⟨fun h ↦ h.indep_delete_of_disjoint hID, fun h ↦ h.of_delete⟩

@[simp] lemma delete_dep_iff : (M ＼ D).Dep X ↔ M.Dep X ∧ Disjoint X D := by
  rw [dep_iff, dep_iff, delete_indep_iff, delete_ground, subset_diff]; tauto

@[simp] lemma delete_base_iff : (M ＼ D).Base B ↔ M.Basis B (M.E \ D) := by
  rw [← restrict_compl, base_restrict_iff]

@[simp] lemma delete_basis_iff : (M ＼ D).Basis I X ↔ M.Basis I X ∧ Disjoint X D := by
  rw [← restrict_compl, basis_restrict_iff, subset_diff, ← and_assoc,
    and_iff_left_of_imp Basis.subset_ground]

@[simp] lemma delete_basis'_iff : (M ＼ D).Basis' I X ↔ M.Basis' I (X \ D) := by
  rw [basis'_iff_basis_inter_ground, delete_basis_iff, delete_ground, diff_eq, inter_comm M.E,
    ← inter_assoc, ← diff_eq, ← basis'_iff_basis_inter_ground, and_iff_left_iff_imp,
    inter_comm, ← inter_diff_assoc]
  exact fun _ ↦ disjoint_sdiff_left

lemma Basis.of_delete (h : (M ＼ D).Basis I X) : M.Basis I X :=
  (delete_basis_iff.mp h).1

lemma Basis.to_delete (h : M.Basis I X) (hX : Disjoint X D) : (M ＼ D).Basis I X := by
  rw [delete_basis_iff]; exact ⟨h, hX⟩

@[simp] lemma delete_loop_iff : (M ＼ D).Loop e ↔ M.Loop e ∧ e ∉ D := by
  rw [← singleton_dep, delete_dep_iff, disjoint_singleton_left, singleton_dep]

@[simp] lemma delete_nonloop_iff : (M ＼ D).Nonloop e ↔ M.Nonloop e ∧ e ∉ D := by
  rw [← indep_singleton, delete_indep_iff, disjoint_singleton_left, indep_singleton]

lemma Nonloop.of_delete (h : (M ＼ D).Nonloop e) : M.Nonloop e :=
  (delete_nonloop_iff.1 h).1

lemma nonloop_iff_delete_of_not_mem (he : e ∉ D) : M.Nonloop e ↔ (M ＼ D).Nonloop e :=
  ⟨fun h ↦ delete_nonloop_iff.2 ⟨h, he⟩, fun h ↦ h.of_delete⟩

@[simp] lemma delete_circuit_iff {C : Set α} :
    (M ＼ D).Circuit C ↔ M.Circuit C ∧ Disjoint C D := by
  simp_rw [circuit_iff, delete_dep_iff, and_imp]
  rw [and_comm, ← and_assoc, and_congr_left_iff, and_comm, and_congr_right_iff]
  exact fun hdj _↦ ⟨fun h I hId hIC ↦ h hId (disjoint_of_subset_left hIC hdj) hIC,
    fun h I hI _ hIC ↦ h hI hIC⟩

lemma Circuit.of_delete {C : Set α} (h : (M ＼ D).Circuit C) : M.Circuit C :=
  (delete_circuit_iff.1 h).1

lemma circuit_iff_delete_of_disjoint {C : Set α} (hCD : Disjoint C D) :
    M.Circuit C ↔ (M ＼ D).Circuit C :=
  ⟨fun h ↦ delete_circuit_iff.2 ⟨h, hCD⟩, fun h ↦ h.of_delete⟩

@[simp] lemma delete_closure_eq (M : Matroid α) (D X : Set α) :
    (M ＼ D).closure X = M.closure (X \ D) \ D := by
  rw [← restrict_compl, restrict_closure_eq', sdiff_sdiff_self, bot_eq_empty, union_empty,
    diff_eq, inter_comm M.E, ← inter_assoc X, ← diff_eq, closure_inter_ground,
    ← inter_assoc, ← diff_eq, inter_eq_left]
  exact diff_subset.trans (M.closure_subset_ground _)

lemma Loopless.delete (h : M.Loopless) (D : Set α) : (M ＼ D).Loopless := by
  simp [loopless_iff_closure_empty]

instance [h : M.Loopless] {D : Set α} : (M ＼ D).Loopless :=
  h.delete D

lemma delete_loops_eq (M : Matroid α) (D : Set α) : (M ＼ D).closure ∅ = M.closure ∅ \ D := by
  simp

@[simp] lemma delete_empty (M : Matroid α) : M ＼ (∅ : Set α) = M := by
  rw [delete_eq_self_iff]; exact empty_disjoint _

lemma delete_delete_diff (M : Matroid α) (D₁ D₂ : Set α) : M ＼ D₁ ＼ D₂ = M ＼ D₁ ＼ (D₂ \ D₁) :=
  by simp

instance delete_finitary (M : Matroid α) [Finitary M] (D : Set α) : Finitary (M ＼ D) := by
  change Finitary (M ↾ (M.E \ D)); infer_instance

instance deleteElem_finitary (M : Matroid α) [Finitary M] (e : α) : Finitary (M ＼ e) := by
  rw [deleteElem]; infer_instance

lemma removeLoops_eq_delete (M : Matroid α) : M.removeLoops = M ＼ M.closure ∅ := by
  rw [← restrict_compl, removeLoops]
  convert rfl using 2
  simp [Set.ext_iff, mem_setOf, Nonloop, Loop, mem_diff, and_comm]

lemma removeLoops_del_eq_removeLoops (h : X ⊆ M.closure ∅) :
    (M ＼ X).removeLoops = M.removeLoops := by
  rw [removeLoops_eq_delete, delete_delete, removeLoops_eq_delete, delete_closure_eq, empty_diff,
    union_diff_self, union_eq_self_of_subset_left h]

lemma Coindep.delete_base_iff (hD : M.Coindep D) : (M ＼ D).Base B ↔ M.Base B ∧ Disjoint B D := by
  rw [Matroid.delete_base_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hss := h.subset
    rw [subset_diff] at hss
    have hcl := h.basis_closure_right
    rw [hD.closure_compl, basis_ground_iff] at hcl
    exact ⟨hcl, hss.2⟩
  exact h.1.basis_ground.basis_subset (by simp [subset_diff, h.1.subset_ground, h.2]) diff_subset

lemma Coindep.delete_rkPos [M.RkPos] (hD : M.Coindep D) : (M ＼ D).RkPos := by
  simp [rkPos_iff_empty_not_base, hD.delete_base_iff, M.empty_not_base]

lemma Coindep.delete_spanning_iff (hD : M.Coindep D) :
    (M ＼ D).Spanning S ↔ M.Spanning S ∧ Disjoint S D := by
  simp only [spanning_iff_exists_base_subset', hD.delete_base_iff, and_assoc, delete_ground,
    subset_diff, and_congr_left_iff, and_imp]
  refine fun hSE hSD ↦ ⟨fun ⟨B, hB, hBD, hBS⟩ ↦ ⟨B, hB, hBS⟩, fun ⟨B, hB, hBS⟩ ↦ ⟨B, hB, ?_, hBS⟩⟩
  exact hSD.mono_left hBS

end Delete

section Contract

variable {C C₁ C₂ : Set α}

class HasContract (α β : Type*) where
  con : α → β → α

infixl:75 " ／ " => HasContract.con

/-- The contraction `M ／ C` is the matroid on `M.E \ C` whose bases are the sets `B \ I` where `B`
  is a base for `M` containing a base `I` for `C`. It is also equal to the dual of `M✶ ＼ C`, and
  is defined this way so we don't have to give a separate proof that it is actually a matroid. -/
def contract (M : Matroid α) (C : Set α) : Matroid α := (M✶ ＼ C)✶

instance conSet {α : Type*} : HasContract (Matroid α) (Set α) :=
  ⟨Matroid.contract⟩

instance conElem {α : Type*} : HasContract (Matroid α) α :=
  ⟨fun M e ↦ M.contract {e}⟩

@[simp] lemma dual_delete_dual_eq_contract (M : Matroid α) (X : Set α) : (M✶ ＼ X)✶ = M ／ X :=
  rfl

@[simp] lemma dual_contract_dual_eq_delete (M : Matroid α) (X : Set α) : (M✶ ／ X)✶ = M ＼ X := by
  rw [← dual_delete_dual_eq_contract, dual_dual, dual_dual]

@[simp] lemma contract_dual_eq_dual_delete (M : Matroid α) (X : Set α) : (M ／ X)✶ = M✶ ＼ X := by
  rw [← dual_delete_dual_eq_contract, dual_dual]

@[simp] lemma delete_dual_eq_dual_contract (M : Matroid α) (X : Set α) : (M ＼ X)✶ = M✶ ／ X := by
  rw [← dual_delete_dual_eq_contract, dual_dual]

@[simp] lemma contract_ground (M : Matroid α) (C : Set α) : (M ／ C).E = M.E \ C := rfl

instance contract_finite [M.Finite] : (M ／ C).Finite := by
  rw [← dual_delete_dual_eq_contract]; infer_instance

instance contractElem_finite [M.Finite] : (M ／ e).Finite :=
  contract_finite

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma contract_ground_subset_ground (M : Matroid α) (C : Set α) : (M ／ C).E ⊆ M.E :=
  (M.contract_ground C).trans_subset diff_subset

@[simp] lemma contract_elem (M : Matroid α) (e : α) : M ／ e = M ／ ({e} : Set α) :=
  rfl

@[simp] lemma contract_contract (M : Matroid α) (C₁ C₂ : Set α) :
    M ／ C₁ ／ C₂ = M ／ (C₁ ∪ C₂) := by
  rw [eq_comm, ← dual_delete_dual_eq_contract, ← delete_delete, ← dual_contract_dual_eq_delete, ←
    dual_contract_dual_eq_delete, dual_dual, dual_dual, dual_dual]

lemma contract_comm (M : Matroid α) (C₁ C₂ : Set α) : M ／ C₁ ／ C₂ = M ／ C₂ ／ C₁ := by
  rw [contract_contract, union_comm, contract_contract]

lemma contract_eq_self_iff : M ／ C = M ↔ Disjoint C M.E := by
  rw [← dual_delete_dual_eq_contract, ← dual_inj, dual_dual, delete_eq_self_iff, dual_ground]

@[simp] lemma contract_empty (M : Matroid α) : M ／ (∅ : Set α) = M := by
  rw [← dual_delete_dual_eq_contract, delete_empty, dual_dual]

lemma contract_contract_diff (M : Matroid α) (C₁ C₂ : Set α) :
    M ／ C₁ ／ C₂ = M ／ C₁ ／ (C₂ \ C₁) := by
  simp

lemma contract_eq_contract_iff : M ／ C₁ = M ／ C₂ ↔ C₁ ∩ M.E = C₂ ∩ M.E := by
  rw [← dual_delete_dual_eq_contract, ← dual_delete_dual_eq_contract, dual_inj,
    delete_eq_delete_iff, dual_ground]

@[simp] lemma contract_inter_ground_eq (M : Matroid α) (C : Set α) : M ／ (C ∩ M.E) = M ／ C := by
  rw [← dual_delete_dual_eq_contract, (show M.E = M✶.E from rfl), delete_inter_ground_eq]; rfl

lemma coindep_contract_iff : (M ／ C).Coindep X ↔ M.Coindep X ∧ Disjoint X C := by
  rw [coindep_def, contract_dual_eq_dual_delete, delete_indep_iff, ← coindep_def]

lemma Coindep.coindep_contract_of_disjoint (hX : M.Coindep X) (hXC : Disjoint X C) :
    (M ／ C).Coindep X :=
  coindep_contract_iff.mpr ⟨hX, hXC⟩

@[simp] lemma contract_cocircuit_iff : (M ／ C).Cocircuit K ↔ M.Cocircuit K ∧ Disjoint K C := by
  rw [cocircuit_def, contract_dual_eq_dual_delete, delete_circuit_iff]

lemma Indep.contract_base_iff (hI : M.Indep I) :
    (M ／ I).Base B ↔ M.Base (B ∪ I) ∧ Disjoint B I := by
  have hIE := hI.subset_ground
  rw [← dual_dual M, ← coindep_def, coindep_iff_exists] at hI
  obtain ⟨B₀, hB₀, hfk⟩ := hI
  rw [← dual_dual M, ← dual_delete_dual_eq_contract, dual_base_iff', dual_base_iff',
    delete_base_iff, dual_dual, delete_ground, diff_diff, union_comm, union_subset_iff,
    subset_diff, ← and_assoc, and_congr_left_iff, dual_ground, and_iff_left hIE, and_congr_left_iff]
  refine fun _ _ ↦
    ⟨fun h ↦ h.base_of_base_subset hB₀ (subset_diff.mpr ⟨hB₀.subset_ground, ?_⟩), fun hB ↦
      hB.basis_of_subset diff_subset (diff_subset_diff_right subset_union_right)⟩
  exact disjoint_of_subset_left hfk disjoint_sdiff_left

lemma Indep.contract_indep_iff (hI : M.Indep I) :
    (M ／ I).Indep J ↔ Disjoint J I ∧ M.Indep (J ∪ I) := by
  simp_rw [indep_iff, hI.contract_base_iff, union_subset_iff]
  exact ⟨fun ⟨B, ⟨hBI, hdj⟩, hJB⟩ ↦
    ⟨disjoint_of_subset_left hJB hdj, _, hBI, hJB.trans subset_union_left,
      subset_union_right⟩,
    fun ⟨hdj, B, hB, hJB, hIB⟩ ↦ ⟨B \ I,⟨by simpa [union_eq_self_of_subset_right hIB],
      disjoint_sdiff_left⟩, subset_diff.2 ⟨hJB, hdj⟩ ⟩⟩

lemma Nonloop.contract_indep_iff (he : M.Nonloop e) :
    (M ／ e).Indep I ↔ e ∉ I ∧ M.Indep (insert e I) := by
  simp [contract_elem, he.indep.contract_indep_iff]

lemma Indep.union_indep_iff_contract_indep (hI : M.Indep I) :
    M.Indep (I ∪ J) ↔ (M ／ I).Indep (J \ I) := by
  rw [hI.contract_indep_iff, and_iff_right disjoint_sdiff_left, diff_union_self, union_comm]

lemma Indep.diff_indep_contract_of_subset (hJ : M.Indep J) (hIJ : I ⊆ J) :
    (M ／ I).Indep (J \ I) := by
  rwa [← (hJ.subset hIJ).union_indep_iff_contract_indep, union_eq_self_of_subset_left hIJ]

lemma Indep.contract_dep_iff (hI : M.Indep I) :
    (M ／ I).Dep J ↔ Disjoint J I ∧ M.Dep (J ∪ I) := by
  rw [dep_iff, hI.contract_indep_iff, dep_iff, contract_ground, subset_diff, disjoint_comm,
    union_subset_iff, and_iff_left hI.subset_ground]
  tauto

lemma Indep.union_basis_union_of_contract_basis (hI : M.Indep I) (hB : (M ／ I).Basis J X) :
    M.Basis (J ∪ I) (X ∪ I) := by
  have hi := hB.indep
  rw [hI.contract_indep_iff] at hi
  refine hi.2.basis_of_maximal_subset (union_subset_union_left _ hB.subset) ?_ ?_
  · intro K hK hJIK hKXI
    rw [union_subset_iff] at hJIK
    have hK' : (M ／ I).Indep (K \ I) := hK.diff_indep_contract_of_subset hJIK.2
    have hm := hB.eq_of_subset_indep hK'
    rw [subset_diff, and_iff_left hi.1, diff_subset_iff, union_comm, imp_iff_right hKXI,
      imp_iff_right hJIK.1] at hm
    simp [hm]
  exact union_subset (hB.subset_ground.trans (contract_ground_subset_ground _ _)) hI.subset_ground

lemma Basis'.contract_basis'_diff_diff_of_subset (hIX : M.Basis' I X) (hJI : J ⊆ I) :
    (M ／ J).Basis' (I \ J) (X \ J) := by
  suffices ∀ ⦃K⦄, Disjoint K J → M.Indep (K ∪ J) → K ⊆ X → I ⊆ K ∪ J → K ⊆ I by
    simpa (config := { contextual := true }) [Basis', (hIX.indep.subset hJI).contract_indep_iff,
      subset_diff, maximal_subset_iff, disjoint_sdiff_left,
      union_eq_self_of_subset_right hJI, hIX.indep, diff_subset.trans hIX.subset,
      diff_subset_iff, subset_antisymm_iff, union_comm J]

  exact fun K hJK hKJi hKX hIJK ↦ by
    simp [hIX.eq_of_subset_indep hKJi hIJK (union_subset hKX (hJI.trans hIX.subset))]

lemma Basis'.contract_basis'_diff_of_subset (hIX : M.Basis' I X) (hJI : J ⊆ I) :
    (M ／ J).Basis' (I \ J) X := by
  rw [basis'_iff_basis_inter_ground]
  simpa [inter_diff_assoc] using (hIX.contract_basis'_diff_diff_of_subset hJI).basis_inter_ground

lemma Basis.contract_basis_diff_diff_of_subset (hIX : M.Basis I X) (hJI : J ⊆ I) :
    (M ／ J).Basis (I \ J) (X \ J) := by
  have h := (hIX.basis'.contract_basis'_diff_of_subset hJI).basis_inter_ground
  rwa [contract_ground, ← inter_diff_assoc, inter_eq_self_of_subset_left hIX.subset_ground] at h

lemma Basis.contract_diff_basis_diff (hIX : M.Basis I X) (hJY : M.Basis J Y) (hIJ : I ⊆ J) :
    (M ／ I).Basis (J \ I) (Y \ X) := by
  refine (hJY.contract_basis_diff_diff_of_subset hIJ).basis_subset ?_ ?_
  · rw [subset_diff, and_iff_right (diff_subset.trans hJY.subset),
      hIX.eq_of_subset_indep (hJY.indep.inter_right X) (subset_inter hIJ hIX.subset)
      inter_subset_right, diff_self_inter]
    exact disjoint_sdiff_left
  refine diff_subset_diff_right hIX.subset

lemma Basis.contract_basis_union_union (h : M.Basis (J ∪ I) (X ∪ I))
    (hJI : Disjoint J I) (hXI : Disjoint X I) : (M ／ I).Basis J X := by
  have  h' : (M ／ I).Basis' J X := by
    simpa [hXI.sdiff_eq_left, hJI.sdiff_eq_left] using
    h.basis'.contract_basis'_diff_diff_of_subset subset_union_right

  rwa [basis'_iff_basis _ ] at h'
  rw [contract_ground, subset_diff, and_iff_left hXI]
  exact subset_union_left.trans h.subset_ground

lemma contract_eq_delete_of_subset_coloops (hX : X ⊆ M✶.closure ∅) : M ／ X = M ＼ X := by
  refine ext_indep rfl fun I _ ↦ ?_
  rw [(indep_of_subset_coloops hX).contract_indep_iff, delete_indep_iff, and_comm,
    union_indep_iff_indep_of_subset_coloops hX]

lemma contract_eq_delete_of_subset_loops (hX : X ⊆ M.closure ∅) : M ／ X = M ＼ X := by
  rw [← dual_inj, contract_dual_eq_dual_delete, delete_dual_eq_dual_contract, eq_comm,
    contract_eq_delete_of_subset_coloops]
  rwa [dual_dual]

lemma Basis.contract_eq_contract_delete (hI : M.Basis I X) : M ／ X = M ／ I ＼ (X \ I) := by
  nth_rw 1 [← diff_union_of_subset hI.subset]
  rw [union_comm, ← contract_contract]
  refine contract_eq_delete_of_subset_loops fun e he ↦ ?_
  rw [← loop_iff_mem_closure_empty, ← singleton_dep, hI.indep.contract_dep_iff,
    disjoint_singleton_left, and_iff_right he.2, singleton_union,
    ← hI.indep.mem_closure_iff_of_not_mem he.2]
  exact hI.subset_closure he.1

lemma Basis'.contract_eq_contract_delete (hI : M.Basis' I X) : M ／ X = M ／ I ＼ (X \ I) := by
  rw [← contract_inter_ground_eq, hI.basis_inter_ground.contract_eq_contract_delete, eq_comm,
    ← delete_inter_ground_eq, contract_ground, diff_eq, diff_eq, ← inter_inter_distrib_right,
    ← diff_eq]

lemma Basis'.contract_indep_iff (hI : M.Basis' I X) :
    (M ／ X).Indep J ↔ M.Indep (J ∪ I) ∧ Disjoint X J := by
  rw [hI.contract_eq_contract_delete, delete_indep_iff, hI.indep.contract_indep_iff,
    and_comm, ← and_assoc, ← disjoint_union_right, diff_union_self,
    union_eq_self_of_subset_right hI.subset, and_comm, disjoint_comm]

lemma Basis.contract_indep_iff (hI : M.Basis I X) :
    (M ／ X).Indep J ↔ M.Indep (J ∪ I) ∧ Disjoint X J :=
  hI.basis'.contract_indep_iff

lemma Basis.contract_indep_diff_iff (hI : M.Basis I X) :
    (M ／ X).Indep (J \ X) ↔ M.Indep ((J \ X) ∪ I) := by
  rw [hI.contract_indep_iff, and_iff_left disjoint_sdiff_right]

lemma Basis'.contract_indep_diff_iff (hI : M.Basis' I X) :
    (M ／ X).Indep (J \ X) ↔ M.Indep ((J \ X) ∪ I) := by
  rw [hI.contract_indep_iff, and_iff_left disjoint_sdiff_right]

lemma contract_closure_eq_contract_delete (M : Matroid α) (C : Set α) :
    M ／ M.closure C = M ／ C ＼ (M.closure C \ C) := by
  obtain ⟨I, hI⟩ := M.exists_basis_inter_ground_basis_closure C
  rw [hI.2.contract_eq_contract_delete, ← M.contract_inter_ground_eq C,
    hI.1.contract_eq_contract_delete, delete_delete]
  convert rfl using 2
  rw [union_comm, diff_eq (t := I), union_inter_distrib_left, union_inter_distrib_left,
    diff_union_self, union_eq_self_of_subset_left (diff_subset.trans (M.closure_subset_ground _)),
      union_inter_distrib_right, diff_eq, inter_eq_self_of_subset_left (M.closure_subset_ground _),
      ← closure_inter_ground, union_eq_self_of_subset_right (M.subset_closure (C ∩ M.E)),
      inter_union_distrib_left, ← inter_assoc, inter_self, ← inter_union_distrib_left,
      ← compl_inter, ← diff_eq,
      inter_eq_self_of_subset_right (hI.1.subset.trans inter_subset_left)]

lemma exists_eq_contract_indep_delete (M : Matroid α) (C : Set α) :
    ∃ I D : Set α, M.Basis I (C ∩ M.E) ∧ D ⊆ (M ／ I).E ∧ D ⊆ C ∧ M ／ C = M ／ I ＼ D := by
  obtain ⟨I, hI⟩ := M.exists_basis (C ∩ M.E)
  use I, C \ I ∩ M.E, hI
  rw [contract_ground, and_iff_right (inter_subset_left.trans diff_subset), diff_eq,
    diff_eq, inter_right_comm, inter_assoc, and_iff_right inter_subset_right,
    ← contract_inter_ground_eq, hI.contract_eq_contract_delete, diff_eq, inter_assoc]

lemma Indep.of_contract (hI : (M ／ C).Indep I) : M.Indep I := by
  obtain ⟨J, R, hJ, -, -, hM⟩ := M.exists_eq_contract_indep_delete C
  rw [hM, delete_indep_iff, hJ.indep.contract_indep_iff] at hI
  exact hI.1.2.subset subset_union_left

instance contract_finiteRk [FiniteRk M] : FiniteRk (M ／ C) := by
  obtain ⟨B, hB⟩ := (M ／ C).exists_base
  refine ⟨B, hB, hB.indep.of_contract.finite⟩

instance contract_finitary [Finitary M] : Finitary (M ／ C) := by
  obtain ⟨J, D, hJ, -, -, hM⟩ := M.exists_eq_contract_indep_delete C
  rw [hM]
  suffices Finitary (M ／ J) by infer_instance
  refine ⟨fun I hI ↦ ?_⟩
  simp_rw [hJ.indep.contract_indep_iff] at hI ⊢
  simp_rw [disjoint_iff_forall_ne]
  refine ⟨fun x hx y hy ↦ ?_, ?_⟩
  · rintro rfl
    specialize hI {x} (singleton_subset_iff.2 hx) (finite_singleton _)
    simp only [disjoint_singleton_left, singleton_union] at hI
    exact hI.1 hy
  apply indep_of_forall_finite_subset_indep _ (fun K hK hKfin ↦ ?_)
  specialize hI (K ∩ I) inter_subset_right (hKfin.subset inter_subset_left)
  refine hI.2.subset <| (subset_inter Subset.rfl hK).trans ?_
  rw [inter_union_distrib_left]
  exact union_subset_union Subset.rfl inter_subset_right

instance contractElem_finiteRk [FiniteRk M] {e : α} : FiniteRk (M ／ e) := by
  rw [contract_elem]; infer_instance

instance contractElem_finitary [Finitary M] {e : α} : Finitary (M ／ e) := by
  rw [contract_elem]; infer_instance

@[simp] lemma contract_loop_iff_mem_closure : (M ／ C).Loop e ↔ e ∈ M.closure C \ C := by
  obtain ⟨I, D, hI, -, -, hM⟩ := M.exists_eq_contract_indep_delete C
  rw [hM, delete_loop_iff, ← singleton_dep, hI.indep.contract_dep_iff, disjoint_singleton_left,
    singleton_union, hI.indep.insert_dep_iff, mem_diff, ← M.closure_inter_ground C,
    hI.closure_eq_closure, and_comm (a := e ∉ I), and_self_right, ← mem_diff, ← mem_diff, diff_diff]
  apply_fun Matroid.E at hM
  rw [delete_ground, contract_ground, contract_ground, diff_diff, diff_eq_diff_iff_inter_eq_inter,
    inter_comm, inter_comm M.E] at hM
  exact
    ⟨fun h ↦ ⟨h.1, fun heC ↦ h.2 (hM.subset ⟨heC, M.closure_subset_ground _ h.1⟩).1⟩, fun h ↦
      ⟨h.1, fun h' ↦ h.2 (hM.symm.subset ⟨h', M.closure_subset_ground _ h.1⟩).1⟩⟩

lemma contract_loops_eq : (M ／ C).closure ∅ = M.closure C \ C := by
  simp [Set.ext_iff, ← loop_iff_mem_closure_empty, contract_loop_iff_mem_closure]

@[simp] lemma contract_closure_eq (M : Matroid α) (C X : Set α) :
    (M ／ C).closure X = M.closure (X ∪ C) \ C := by
  ext e
  by_cases heX : e ∈ X
  · by_cases he : e ∈ (M ／ C).E
    · refine iff_of_true (mem_closure_of_mem' _ heX) ?_
      rw [contract_ground] at he
      exact ⟨mem_closure_of_mem' _ (Or.inl heX) he.1, he.2⟩
    refine iff_of_false (he ∘ fun h ↦ closure_subset_ground _ _ h) (he ∘ fun h ↦ ?_)
    rw [contract_ground]
    exact ⟨M.closure_subset_ground _ h.1, h.2⟩
  suffices h' : e ∈ (M ／ C).closure X \ X ↔ e ∈ M.closure (X ∪ C) \ (X ∪ C) by
    rwa [mem_diff, and_iff_left heX, mem_diff, mem_union, or_iff_right heX, ← mem_diff] at h'
  rw [← contract_loop_iff_mem_closure, ← contract_loop_iff_mem_closure, contract_contract,
    union_comm]

lemma Circuit.contract_dep (hK : M.Circuit K) (hCK : Disjoint C K) : (M ／ C).Dep K := by
  obtain ⟨I, hI⟩ := M.exists_basis (C ∩ M.E)
  rw [← contract_inter_ground_eq, Dep, hI.contract_indep_iff,
    and_iff_left (hCK.mono_left inter_subset_left), contract_ground, subset_diff,
    and_iff_left (hCK.symm.mono_right inter_subset_left), and_iff_left hK.subset_ground]
  exact fun hi ↦ hK.dep.not_indep (hi.subset subset_union_left)

lemma Circuit.contract_circuit (hK : M.Circuit K) (hC : C ⊂ K) : (M ／ C).Circuit (K \ C) := by
  have hCi := hK.ssubset_indep hC
  rw [circuit_iff_forall_ssubset, hCi.contract_dep_iff, and_iff_right (disjoint_sdiff_left),
    diff_union_self, union_eq_self_of_subset_right hC.subset, and_iff_right hK.dep]
  intro I hI
  rw [ssubset_iff_subset_not_subset, subset_diff, diff_subset_iff, union_comm] at hI
  rw [hCi.contract_indep_iff, and_iff_right hI.1.2]
  refine hK.ssubset_indep <| (union_subset hI.1.1 hC.subset).ssubset_of_ne ?_
  rintro rfl
  exact hI.2 Subset.rfl

lemma Circuit.contractElem_circuit (hC : M.Circuit C) (hnt : C.Nontrivial) (heC : e ∈ C) :
    (M ／ e).Circuit (C \ {e}) :=
  hC.contract_circuit (ssubset_of_ne_of_subset hnt.ne_singleton.symm (by simpa))

lemma Circuit.contract_dep_of_not_subset (hK : M.Circuit K) {C : Set α} (hKC : ¬ K ⊆ C) :
    (M ／ C).Dep (K \ C) := by
  have h' := hK.contract_circuit (C := C ∩ K) (inter_subset_right.ssubset_of_ne (by simpa))
  simp only [diff_inter_self_eq_diff] at h'
  have hwin := h'.contract_dep (C := C \ K) disjoint_sdiff_sdiff
  rwa [contract_contract, inter_union_diff] at hwin

lemma Circuit.contract_diff_circuit (hC : M.Circuit C) (hK : K.Nonempty) (hKC : K ⊆ C) :
    (M ／ (C \ K)).Circuit K := by
  simpa [inter_eq_self_of_subset_right hKC] using hC.contract_circuit (diff_ssubset hKC hK)

lemma Circuit.subset_circuit_of_contract {C K : Set α} (hC : (M ／ K).Circuit C) :
    ∃ C', M.Circuit C' ∧ C ⊆ C' ∧ C' ⊆ C ∪ K := by
  obtain ⟨I, hI⟩ := M.exists_basis' K
  rw [hI.contract_eq_contract_delete, delete_circuit_iff] at hC

  have hCss := hC.1.subset_ground
  rw [contract_ground, subset_diff] at hCss
  obtain ⟨hCE, hCI⟩ := hCss
  have hIE := hI.indep.subset_ground

  have hCId : M.Dep (C ∪ I) := by
    rw [← not_indep_iff]; intro hd
    have hCi := hd.diff_indep_contract_of_subset subset_union_right
    rw [union_diff_right, sdiff_eq_left.2 hCI] at hCi
    exact hC.1.dep.not_indep hCi

  obtain ⟨C', hC'CI, hC'⟩ := hCId.exists_circuit_subset
  refine ⟨C', hC', ?_, hC'CI.trans (union_subset_union_right _ hI.subset)⟩

  have hd := hC'.contract_dep_of_not_subset (C := I)
    (fun hC'I ↦ (hI.indep.subset hC'I).not_dep hC'.dep)
  rw [← hC.1.eq_of_dep_subset hd (by simpa [diff_subset_iff, union_comm])]
  exact diff_subset

lemma Dep.of_contract (h : (M ／ C).Dep X) (hC : C ⊆ M.E := by aesop_mat) : M.Dep (C ∪ X) := by
  rw [Dep, and_iff_left (union_subset hC (h.subset_ground.trans diff_subset))]
  intro hi
  rw [Dep, (hi.subset subset_union_left).contract_indep_iff, union_comm,
    and_iff_left hi] at h
  exact h.1 (subset_diff.1 h.2).2

lemma Basis.diff_subset_loops_contract (hIX : M.Basis I X) : X \ I ⊆ (M ／ I).closure ∅ := by
  rw [diff_subset_iff, contract_loops_eq, union_diff_self,
    union_eq_self_of_subset_left (M.subset_closure I)]
  exact hIX.subset_closure

lemma contract_spanning_iff' (M : Matroid α) (C X : Set α) :
    (M ／ C).Spanning X ↔ M.Spanning (X ∪ (C ∩ M.E)) ∧ Disjoint X C := by
  simp_rw [spanning_iff, contract_closure_eq, contract_ground, subset_diff, union_subset_iff,
    and_iff_left inter_subset_right, ← and_assoc, and_congr_left_iff,
    subset_antisymm_iff, subset_diff, diff_subset_iff, and_iff_left disjoint_sdiff_left,
    and_iff_right (M.closure_subset_ground _ ),
    and_iff_right (subset_union_of_subset_right (M.closure_subset_ground _) C)]
  rw [← inter_eq_left (s := M.E), inter_union_distrib_left,
    inter_eq_self_of_subset_right (M.closure_subset_ground _), subset_antisymm_iff,
    union_subset_iff, and_iff_right inter_subset_left, union_eq_self_of_subset_left (s := M.E ∩ C),
    and_iff_right (M.closure_subset_ground _), Iff.comm,
    closure_union_congr_right (M.closure_inter_ground _)]
  · exact fun _ _ ↦ Iff.rfl
  exact (M.subset_closure _).trans
    (M.closure_subset_closure (inter_subset_right.trans subset_union_right))

lemma contract_spanning_iff (hC : C ⊆ M.E := by aesop_mat) :
    (M ／ C).Spanning X ↔ M.Spanning (X ∪ C) ∧ Disjoint X C := by
  rw [contract_spanning_iff', inter_eq_self_of_subset_left hC]

lemma Spanning.contract (hX : M.Spanning X) (C : Set α) : (M ／ C).Spanning (X \ C) := by
  rw [contract_spanning_iff', and_iff_left disjoint_sdiff_left,
    diff_eq_diff_inter_of_subset hX.subset_ground C, diff_union_self]
  apply hX.superset subset_union_left

lemma Spanning.contract_eq_loopyOn (hX : M.Spanning X) : M ／ X = loopyOn (M.E \ X) := by
  rw [eq_loopyOn_iff_closure]
  simp [hX.closure_eq]

lemma Nonloop.of_contract (h : (M ／ C).Nonloop e) : M.Nonloop e := by
  rw [← indep_singleton] at h ⊢
  exact h.of_contract

@[simp] lemma contract_nonloop_iff : (M ／ C).Nonloop e ↔ e ∈ M.E \ M.closure C := by
  rw [nonloop_iff_mem_compl_loops, contract_ground, contract_loops_eq]
  refine ⟨fun ⟨he,heC⟩ ↦ ⟨he.1, fun h ↦ heC ⟨h, he.2⟩⟩,
    fun h ↦ ⟨⟨h.1, fun heC ↦ h.2 ?_⟩, fun h' ↦ h.2 h'.1⟩⟩
  rw [← closure_inter_ground]
  exact (M.subset_closure (C ∩ M.E)) ⟨heC, h.1⟩

lemma Cocircuit.of_contract (hK : (M ／ C).Cocircuit K) : M.Cocircuit K := by
  rw [cocircuit_def, contract_dual_eq_dual_delete] at hK
  exact hK.of_delete

lemma Cocircuit.delete_cocircuit {D : Set α} (hK : M.Cocircuit K) (hD : D ⊂ K) :
    (M ＼ D).Cocircuit (K \ D) := by
  rw [cocircuit_def, delete_dual_eq_dual_contract]
  exact hK.circuit.contract_circuit hD

lemma Cocircuit.delete_diff_cocircuit {X : Set α} (hK : M.Cocircuit K) (hXK : X ⊆ K)
    (hX : X.Nonempty) : (M ＼ (K \ X)).Cocircuit X := by
  rw [cocircuit_def, delete_dual_eq_dual_contract]
  exact hK.circuit.contract_diff_circuit hX hXK

end Contract

section Minor

variable {M₀ M₁ M₂ : Matroid α}

lemma contract_delete_diff (M : Matroid α) (C D : Set α) : M ／ C ＼ D = M ／ C ＼ (D \ C) := by
  rw [delete_eq_delete_iff, contract_ground, diff_eq, diff_eq, ← inter_inter_distrib_right,
    inter_assoc]

lemma contract_restrict_eq_restrict_contract (M : Matroid α) (C R : Set α) (h : Disjoint C R) :
    (M ／ C) ↾ R = (M ↾ (R ∪ C)) ／ C := by
  refine ext_indep (by simp [h.sdiff_eq_right]) (fun I _ ↦ ?_)
  obtain ⟨J, hJ⟩ := (M ↾ (R ∪ C)).exists_basis' C
  have hJ' : M.Basis' J C := by
    have := (basis'_restrict_iff.1 hJ).1
    rwa [inter_eq_self_of_subset_left subset_union_right] at this
  rw [restrict_indep_iff, hJ.contract_indep_iff, hJ'.contract_indep_iff, restrict_indep_iff,
    union_subset_iff, and_iff_left (hJ.subset.trans subset_union_right), union_comm R C,
    ← diff_subset_iff, and_assoc, and_assoc, and_congr_right_iff, and_comm, and_congr_left_iff]
  intro _ hd
  rw [hd.sdiff_eq_right]

lemma restrict_contract_eq_contract_restrict (M : Matroid α) {C R : Set α} (hCR : C ⊆ R) :
    (M ↾ R) ／ C = (M ／ C) ↾ (R \ C) := by
  rw [contract_restrict_eq_restrict_contract _ _ _ disjoint_sdiff_right]
  simp [union_eq_self_of_subset_right hCR]

/- TODO : Simplify this proof using the lemma above-/
lemma contract_delete_comm (M : Matroid α) {C D : Set α} (hCD : Disjoint C D) :
    M ／ C ＼ D = M ＼ D ／ C := by
  refine ext_indep (by simp [diff_diff_comm]) (fun I hI ↦ ?_)
  rw [delete_ground, contract_ground, subset_diff, subset_diff] at hI
  simp only [delete_ground, contract_ground, delete_indep_iff, and_iff_left hI.2]
  obtain ⟨J, hJ⟩ := (M ＼ D).exists_basis' C;  have hJ' := hJ
  rw [← restrict_compl, basis'_restrict_iff, subset_diff, diff_eq, inter_comm M.E, ← inter_assoc,
    ← diff_eq, sdiff_eq_left.2 hCD] at hJ'
  rw [hJ.contract_eq_contract_delete, delete_indep_iff, hJ.indep.contract_indep_iff,
    delete_indep_iff, ← contract_inter_ground_eq, hJ'.1.contract_eq_contract_delete,
    delete_indep_iff,  hJ'.1.indep.contract_indep_iff, disjoint_union_left, and_iff_right hI.2,
    and_iff_left (disjoint_of_subset_right diff_subset hI.1.2), and_iff_left hJ'.2.2,
    and_iff_left
    (disjoint_of_subset_right (diff_subset.trans inter_subset_left) hI.1.2)]

lemma contract_delete_comm' (M : Matroid α) (C D : Set α) : M ／ C ＼ D = M ＼ (D \ C) ／ C := by
  rw [contract_delete_diff, contract_delete_comm _ disjoint_sdiff_right]

lemma delete_contract_diff (M : Matroid α) (D C : Set α) : M ＼ D ／ C = M ＼ D ／ (C \ D) := by
  rw [contract_eq_contract_iff, delete_ground, diff_inter_diff_right, diff_eq, diff_eq, inter_assoc]

lemma delete_contract_comm' (M : Matroid α) (D C : Set α) : M ＼ D ／ C = M ／ (C \ D) ＼ D := by
  rw [delete_contract_diff, ← contract_delete_comm _ disjoint_sdiff_left]

lemma contract_delete_contract' (M : Matroid α) (C D C' : Set α) :
    M ／ C ＼ D ／ C' = M ／ (C ∪ C' \ D) ＼ D := by
  rw [delete_contract_diff, ← contract_delete_comm _ disjoint_sdiff_left, contract_contract]

lemma contract_delete_contract (M : Matroid α) (C D C' : Set α) (h : Disjoint C' D) :
    M ／ C ＼ D ／ C' = M ／ (C ∪ C') ＼ D := by rw [contract_delete_contract', sdiff_eq_left.mpr h]

lemma contract_delete_contract_delete' (M : Matroid α) (C D C' D' : Set α) :
    M ／ C ＼ D ／ C' ＼ D' = M ／ (C ∪ C' \ D) ＼ (D ∪ D') := by
  rw [contract_delete_contract', delete_delete]

lemma contract_delete_contract_delete (M : Matroid α) (C D C' D' : Set α) (h : Disjoint C' D) :
    M ／ C ＼ D ／ C' ＼ D' = M ／ (C ∪ C') ＼ (D ∪ D') := by
  rw [contract_delete_contract_delete', sdiff_eq_left.mpr h]

lemma delete_contract_delete' (M : Matroid α) (D C D' : Set α) :
    M ＼ D ／ C ＼ D' = M ／ (C \ D) ＼ (D ∪ D') := by
  rw [delete_contract_comm', delete_delete]

lemma delete_contract_delete (M : Matroid α) (D C D' : Set α) (h : Disjoint C D) :
    M ＼ D ／ C ＼ D' = M ／ C ＼ (D ∪ D') := by
  rw [delete_contract_delete', sdiff_eq_left.mpr h]

/- `N` is a minor of `M` if `N = M ／ C ＼ D` for disjoint sets `C,D ⊆ M.E`-/
def Minor (N M : Matroid α) : Prop :=
  ∃ C D, C ⊆ M.E ∧ D ⊆ M.E ∧ Disjoint C D ∧ N = M ／ C ＼ D

def StrictMinor (N M : Matroid α) : Prop :=
  Minor N M ∧ ¬Minor M N

infixl:50 " ≤m " => Matroid.Minor
infixl:50 " <m " => Matroid.StrictMinor

lemma contract_delete_minor (M : Matroid α) (C D : Set α) : M ／ C ＼ D ≤m M := by
  rw [contract_delete_diff, ← contract_inter_ground_eq, ← delete_inter_ground_eq,
    contract_ground, diff_inter_self_eq_diff, diff_inter_diff_right, inter_diff_right_comm]
  refine ⟨_,_, inter_subset_right, inter_subset_right, ?_, rfl⟩
  exact disjoint_of_subset inter_subset_left inter_subset_left disjoint_sdiff_right

lemma minor_def : N ≤m M ↔ ∃ C D, C ⊆ M.E ∧ D ⊆ M.E ∧ Disjoint C D ∧ N = M ／ C ＼ D := Iff.rfl

lemma minor_iff_exists_contract_delete : N ≤m M ↔ ∃ C D : Set α, N = M ／ C ＼ D :=
  ⟨fun ⟨C, D, h⟩ ↦ ⟨_,_,h.2.2.2⟩, fun ⟨C, D, h⟩ ↦ by rw [h]; apply contract_delete_minor⟩

lemma Indep.of_minor (hI : N.Indep I) (hNM : N ≤m M) : M.Indep I := by
  obtain ⟨C,D, rfl⟩ := minor_iff_exists_contract_delete.1 hNM
  exact hI.of_delete.of_contract

lemma Nonloop.of_minor (h : N.Nonloop e) (hNM : N ≤m M) : M.Nonloop e := by
  obtain ⟨C, D, rfl⟩ := minor_iff_exists_contract_delete.1 hNM
  exact h.of_delete.of_contract

lemma Loop.minor (he : M.Loop e) (heN : e ∈ N.E) (hNM : N ≤m M) : N.Loop e := by
  rw [← not_nonloop_iff]
  exact fun hnl ↦ he.not_nonloop <| hnl.of_minor hNM

lemma Minor.eq_of_ground_subset (h : N ≤m M) (hE : M.E ⊆ N.E) : M = N := by
  obtain ⟨C, D, -, -, -, rfl⟩ := h
  rw [delete_ground, contract_ground, subset_diff, subset_diff] at hE
  rw [← contract_inter_ground_eq, hE.1.2.symm.inter_eq, contract_empty, ← delete_inter_ground_eq,
    hE.2.symm.inter_eq, delete_empty]

lemma Minor.subset (h : N ≤m M) : N.E ⊆ M.E := by
  obtain ⟨C, D, -, -, -, rfl⟩ := h; exact diff_subset.trans diff_subset

lemma Minor.refl {M : Matroid α} : M ≤m M :=
  minor_iff_exists_contract_delete.2 ⟨∅, ∅, by simp⟩

lemma Minor.trans {M₁ M₂ M₃ : Matroid α} (h : M₁ ≤m M₂) (h' : M₂ ≤m M₃) : M₁ ≤m M₃ := by
  obtain ⟨C₁, D₁, -, -, -, rfl⟩ := h
  obtain ⟨C₂, D₂, -, -, -, rfl⟩ := h'
  rw [contract_delete_contract_delete']
  apply contract_delete_minor

lemma Minor.antisymm (h : N ≤m M) (h' : M ≤m N) : N = M :=
  h'.eq_of_ground_subset h.subset

/-- The minor order is a `PartialOrder` on `Matroid α`. We prefer the spelling `M ≤m M'`
  to `M ≤ M'` for the dot notation. -/
instance (α : Type*) : PartialOrder (Matroid α) where
  le M M' := M ≤m M'
  lt M M' := M <m M'
  le_refl M := Minor.refl
  le_trans _ _ _ h h' := Minor.trans h h'
  le_antisymm _ _ h h' := Minor.antisymm h h'

lemma Minor.finite (h : N ≤m M) [M.Finite] : N.Finite :=
  ⟨M.ground_finite.subset h.subset⟩

lemma Minor.finiteRk (h : N ≤m M) [FiniteRk M] : FiniteRk N := by
  obtain ⟨C, D, rfl⟩ := minor_iff_exists_contract_delete.1 h
  infer_instance

lemma Minor.finitary (h : N ≤m M) [Finitary M] : Finitary N := by
  obtain ⟨C, D, rfl⟩ := minor_iff_exists_contract_delete.1 h
  infer_instance

lemma Minor.le (h : N ≤m M) : N ≤ M := h

lemma StrictMinor.lt (h : N <m M) : N < M := h

@[simp] protected lemma le_iff (M M' : Matroid α) : M ≤ M' ↔ M ≤m M' := Iff.rfl

@[simp] protected lemma lt_iff (M M' : Matroid α) : M < M' ↔ M <m M' := Iff.rfl

lemma StrictMinor.minor (h : N <m M) : N ≤m M :=
  h.lt.le

lemma StrictMinor.not_minor (h : N <m M) : ¬ (M ≤m N) :=
  h.lt.not_le

lemma strictMinor_iff_minor_ne : N <m M ↔ N ≤m M ∧ N ≠ M :=
  lt_iff_le_and_ne (α := Matroid α)

lemma StrictMinor.ne (h : N <m M) : N ≠ M :=
  LT.lt.ne h

lemma strictMinor_irrefl (M : Matroid α) : ¬ (M <m M) :=
  lt_irrefl M

lemma StrictMinor.ssubset (h : N <m M) : N.E ⊂ M.E :=
  h.minor.subset.ssubset_of_ne (fun hE ↦ h.ne (h.minor.eq_of_ground_subset hE.symm.subset).symm)

lemma strictMinor_iff_minor_ssubset : N <m M ↔ N ≤m M ∧ N.E ⊂ M.E :=
  ⟨fun h ↦ ⟨h.minor, h.ssubset⟩, fun ⟨h, hss⟩ ↦ ⟨h, fun h' ↦ hss.ne <| by rw [h'.antisymm h]⟩⟩

lemma StrictMinor.trans_minor (h : N <m M) (h' : M ≤m M') : N <m M' :=
  h.lt.trans_le h'

lemma Minor.trans_strictMinor (h : N ≤m M) (h' : M <m M') : N <m M' :=
  h.le.trans_lt h'

lemma StrictMinor.trans (h : N <m M) (h' : M <m M') : N <m M' :=
  h.lt.trans h'

lemma strictMinor_iff_exists_eq_contract_delete :
    N <m M ↔ ∃ C D, C ⊆ M.E ∧ D ⊆ M.E ∧ Disjoint C D ∧ (C ∪ D).Nonempty ∧ N = M ／ C ＼ D := by
  rw [strictMinor_iff_minor_ssubset, minor_def]
  constructor
  rintro ⟨⟨C, D, hC, hD, hCD, rfl⟩, hss⟩
  · refine ⟨C, D, hC, hD, hCD, ?_, rfl⟩
    rw [nonempty_iff_ne_empty]; rintro hCD
    rw [delete_ground, contract_ground, diff_diff, hCD, diff_empty] at hss
    exact hss.ne rfl
  rintro ⟨C, D, hC, hD, hCD, ⟨e,he⟩, rfl⟩
  use ⟨C, D, hC, hD, hCD, rfl⟩
  rw [delete_ground, contract_ground, diff_diff, ssubset_iff_subset_not_subset,
    and_iff_right diff_subset]
  exact fun hss ↦ (hss ((union_subset hC hD) he)).2 he

lemma contract_minor (M : Matroid α) (C : Set α) : M ／ C ≤m M := by
  rw [← (M ／ C).delete_empty]; apply contract_delete_minor

lemma contract_minor_of_subset (M : Matroid α) {C C' : Set α} (hCC' : C ⊆ C') :
    M ／ C' ≤m M ／ C := by
  rw [← diff_union_of_subset hCC', union_comm, ← contract_contract]
  apply contract_minor

lemma contract_minor_of_mem (M : Matroid α) {C : Set α} (he : e ∈ C) :
    M ／ C ≤m M ／ e :=
  M.contract_minor_of_subset (singleton_subset_iff.2 he)

lemma delete_minor (M : Matroid α) (D : Set α) : M ＼ D ≤m M := by
  nth_rw 1 [← M.contract_empty]; apply contract_delete_minor

lemma restrict_minor (M : Matroid α) (hR : R ⊆ M.E := by aesop_mat) : (M ↾ R) ≤m M := by
  rw [← delete_compl]; apply delete_minor

lemma Restriction.minor (h : N ≤r M) : N ≤m M := by
  rw [← h.eq_restrict, ← delete_compl h.subset]; apply delete_minor

lemma StrictRestriction.strictMinor (h : N <r M) : N <m M :=
  ⟨h.restriction.minor, fun h' ↦ h.ssubset.not_subset h'.subset⟩

lemma restrict_strictMinor (hR : R ⊂ M.E) : M ↾ R <m M :=
  (restrict_strictRestriction hR).strictMinor

lemma delete_contract_minor (M : Matroid α) (D C : Set α) : M ＼ D ／ C ≤m M :=
  ((M ＼ D).contract_minor C).trans (M.delete_minor D)

lemma contract_restrict_minor (M : Matroid α) (C : Set α) (hR : R ⊆ M.E \ C) :
    (M ／ C) ↾ R ≤m M := by
  rw [← delete_compl]; apply contract_delete_minor

lemma contractElem_strictMinor (he : e ∈ M.E) : M ／ e <m M :=
  ⟨contract_minor M {e}, fun hM ↦ (hM.subset he).2 rfl⟩

lemma deleteElem_strictMinor (he : e ∈ M.E) : M ＼ e <m M :=
  ⟨delete_minor M {e}, fun hM ↦ (hM.subset he).2 rfl⟩

lemma strictMinor_iff_minor_contract_or_delete :
    N <m M ↔ ∃ e ∈ M.E, N ≤m M ／ e ∨ N ≤m M ＼ e := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨C, D, hC, hD, hCD, ⟨e,(heC | heD)⟩, rfl⟩ :=
      strictMinor_iff_exists_eq_contract_delete.1 h
    · refine ⟨e, hC heC, Or.inl ?_⟩
      rw [← insert_eq_of_mem heC, ← singleton_union, ← contract_contract, contract_elem ]
      apply contract_delete_minor
    refine ⟨e, hD heD, Or.inr ?_⟩
    rw [contract_delete_comm _ hCD, ← insert_eq_of_mem heD, ← singleton_union, ← delete_delete]
    apply delete_contract_minor
  rintro ⟨e, he, (hc | hd)⟩
  · exact hc.trans_strictMinor (contractElem_strictMinor he)
  exact hd.trans_strictMinor (deleteElem_strictMinor he)

lemma Minor.strictMinor_or_eq (h : N ≤m M) : N <m M ∨ N = M := by
  rw [strictMinor_iff_minor_ne, and_iff_right h]
  exact ne_or_eq N M

lemma Minor.dual (h : N ≤m M) : N✶ ≤m M✶ := by
  obtain ⟨C, D, -, -, -, rfl⟩ := h
  rw [delete_dual_eq_dual_contract, contract_dual_eq_dual_delete]
  apply delete_contract_minor

lemma Minor.of_dual (h : N✶ ≤m M✶) : N ≤m M := by
  simpa using h.dual

lemma dual_minor_iff : N✶ ≤m M✶ ↔ N ≤m M :=
  ⟨Minor.of_dual, Minor.dual⟩

lemma minor_dual_iff_dual_minor : N ≤m M✶ ↔ N✶ ≤m M := by
  rw [← dual_minor_iff, dual_dual]

lemma StrictMinor.dual (h : N <m M) : N✶ <m M✶ := by
  rwa [StrictMinor, dual_minor_iff, dual_minor_iff]

lemma StrictMinor.of_dual (h : N✶ <m M✶) : N <m M := by
  simpa using h.dual

lemma dual_strictMinor_iff: N✶ <m M✶ ↔ N <m M :=
  ⟨StrictMinor.of_dual, StrictMinor.dual⟩

lemma strictMinor_dual_iff_dual_strictMinor : N <m M✶ ↔ N✶ <m M := by
  rw [← dual_strictMinor_iff, dual_dual]

lemma StrictMinor.encard_ground_lt [M.Finite] (hNM : N <m M) : N.E.encard < M.E.encard :=
  M.ground_finite.encard_lt_encard hNM.ssubset

/-- The scum theorem. We can always realize a minor by contracting an independent set and deleting
  a coindependent set -/
lemma Minor.exists_contract_indep_delete_coindep (h : N ≤m M) :
    ∃ C D, M.Indep C ∧ M.Coindep D ∧ Disjoint C D ∧ N = M ／ C ＼ D := by
  obtain ⟨C', D', hC', hD', hCD', rfl⟩ := h
  obtain ⟨I, hI⟩ := M.exists_basis C'
  obtain ⟨K, hK⟩ := M✶.exists_basis D'
  have hIK : Disjoint I K := disjoint_of_subset hI.subset hK.subset hCD'
  use I ∪ D' \ K, C' \ I ∪ K
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hss : (D' \ K) \ I ⊆ (M✶ ／ K ＼ I).closure ∅ := by
      rw [delete_loops_eq];
      exact diff_subset_diff_left hK.diff_subset_loops_contract
    rw [← delete_dual_eq_dual_contract, ← contract_dual_eq_dual_delete] at hss
    have hi := indep_of_subset_coloops hss
    rw [← contract_delete_comm _ hIK, delete_indep_iff, hI.indep.contract_indep_iff,
      diff_union_self, union_comm] at hi
    exact hi.1.2
  · rw [coindep_def]
    have hss : (C' \ I) \ K ⊆ (M ／ I ＼ K)✶✶.closure ∅ := by
      rw [dual_dual, delete_loops_eq];
      exact diff_subset_diff_left hI.diff_subset_loops_contract
    have hi := indep_of_subset_coloops hss
    rw [delete_dual_eq_dual_contract, contract_dual_eq_dual_delete, ←
      contract_delete_comm _ hIK.symm, delete_indep_iff, hK.indep.contract_indep_iff,
      diff_union_self] at hi
    exact hi.1.2
  · rw [disjoint_union_left, disjoint_union_right, disjoint_union_right,
      and_iff_right disjoint_sdiff_right, and_iff_right hIK, and_iff_left disjoint_sdiff_left]
    exact disjoint_of_subset diff_subset diff_subset hCD'.symm
  have hb : (M ／ C')✶.Basis K D' :=
    by
    rw [contract_dual_eq_dual_delete, delete_basis_iff, and_iff_right hK]
    exact hCD'.symm
  rw [← dual_dual (M ／ C' ＼ D'), delete_dual_eq_dual_contract, hb.contract_eq_contract_delete,
    hI.contract_eq_contract_delete, delete_dual_eq_dual_contract, contract_dual_eq_dual_delete,
    dual_dual, delete_delete, contract_delete_contract]
  rw [disjoint_union_right, and_iff_left disjoint_sdiff_left]
  exact disjoint_of_subset diff_subset diff_subset hCD'.symm

lemma Minor.exists_spanning_restriction_contract (h : N ≤m M) :
    ∃ C, M.Indep C ∧ (N ≤r M ／ C) ∧ (M ／ C).closure N.E = (M ／ C).E := by
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := h.exists_contract_indep_delete_coindep
  refine ⟨C, hC, delete_restriction _ _, ?_⟩
  rw [← (hD.coindep_contract_of_disjoint hCD.symm).closure_compl, delete_ground]

lemma Minor.exists_eq_contract_spanning_restrict (h : N ≤m M) :
    ∃ I R, M.Indep I ∧ Disjoint I R ∧ (M ／ I).Spanning R ∧ N = (M ／ I) ↾ R := by
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := h.exists_contract_indep_delete_coindep
  refine ⟨C, (M.E \ C) \ D, hC, disjoint_sdiff_right.mono_right diff_subset, ?_⟩
  rw [contract_spanning_iff, diff_diff_comm, diff_union_self, and_iff_left disjoint_sdiff_left,
    delete_eq_restrict, contract_ground, diff_diff_comm, and_iff_left rfl,
    union_eq_self_of_subset_right (subset_diff.2 ⟨hC.subset_ground, hCD⟩)]
  exact hD.compl_spanning

/-- Classically choose an independent contract-set from a proof that `N` is a minor of `M`. -/
def Minor.C (h : N ≤m M) : Set α :=
  h.exists_contract_indep_delete_coindep.choose

/-- Classically choose a coindependent delete-set from a proof that `N` is a minor of `M`. -/
def Minor.D (h : N ≤m M) : Set α :=
  h.exists_contract_indep_delete_coindep.choose_spec.choose

lemma Minor.C_indep (h : N ≤m M) : M.Indep h.C := by
  obtain ⟨-,h,-⟩ := h.exists_contract_indep_delete_coindep.choose_spec; exact h

lemma Minor.D_coindep (h : N ≤m M) : M.Coindep h.D := by
  obtain ⟨-,h,-⟩ := h.exists_contract_indep_delete_coindep.choose_spec.choose_spec; exact h

lemma Minor.disjoint (h : N ≤m M) : Disjoint h.C h.D := by
  obtain ⟨-,-,h,-⟩ := h.exists_contract_indep_delete_coindep.choose_spec.choose_spec; exact h

lemma Minor.eq_con_del (h : N ≤m M) : N = M ／ h.C ＼ h.D := by
  obtain ⟨-,-,-,h⟩ := h.exists_contract_indep_delete_coindep.choose_spec.choose_spec; exact h

lemma Minor.C_union_D_eq (h : N ≤m M) : h.C ∪ h.D = M.E \ N.E := by
  simp only [h.eq_con_del, delete_ground, contract_ground, diff_diff]
  rw [Set.diff_diff_cancel_left]
  exact union_subset h.C_indep.subset_ground h.D_coindep.subset_ground

lemma Minor.C_disjoint (h : N ≤m M) : Disjoint h.C N.E :=
  (subset_diff.1 h.C_union_D_eq.subset).2.mono_left subset_union_left

lemma Minor.D_disjoint (h : N ≤m M) : Disjoint h.D N.E :=
  (subset_diff.1 h.C_union_D_eq.subset).2.mono_left subset_union_right

lemma Minor.eq_con_restr (h : N ≤m M) : N = (M ／ h.C) ↾ N.E := by
  simp [h.eq_con_del, ← restrict_compl]

lemma StrictMinor.C_union_D_nonempty (h : N <m M) : (h.minor.C ∪ h.minor.D).Nonempty := by
  rw [h.minor.C_union_D_eq]
  exact nonempty_of_ssubset h.ssubset

lemma finite_setOf_minor (M : Matroid α) [M.Finite] : {N | N ≤m M}.Finite :=
  (finite_setOf_matroid M.ground_finite).subset (fun _ hNM ↦ hNM.subset)

end Minor

section Constructions

variable {E : Set α}

@[simp] lemma delete_ground_self (M : Matroid α) : M ＼ M.E = emptyOn α := by
  simp [← ground_eq_empty_iff]

@[simp] lemma contract_ground_self (M : Matroid α) : M ／ M.E = emptyOn α := by
  simp [← ground_eq_empty_iff]

@[simp] lemma emptyOn_restriction (M : Matroid α) : emptyOn α ≤r M :=
  ⟨∅, empty_subset _, by simp⟩

@[simp] lemma emptyOn_minor (M : Matroid α) : emptyOn α ≤m M :=
  M.emptyOn_restriction.minor

@[simp] lemma minor_emptyOn_iff : M ≤m emptyOn α ↔ M = emptyOn α :=
  ⟨fun h ↦ ground_eq_empty_iff.1 (eq_empty_of_subset_empty h.subset),
    by rintro rfl; apply emptyOn_minor⟩

@[simp] lemma restriction_emptyOn_iff : M ≤r emptyOn α ↔ M = emptyOn α := by
  refine ⟨fun h ↦ minor_emptyOn_iff.1 h.minor, ?_⟩
  rintro rfl
  exact Restriction.refl

@[simp] lemma loopyOn_delete (E X : Set α) : (loopyOn E) ＼ X = loopyOn (E \ X) := by
  rw [← restrict_compl, loopyOn_restrict, loopyOn_ground]

@[simp] lemma loopyOn_contract (E X : Set α) : (loopyOn E) ／ X = loopyOn (E \ X) := by
  simp_rw [eq_loopyOn_iff_closure, contract_closure_eq, empty_union, loopyOn_closure_eq,
    contract_ground, loopyOn_ground, true_and]

@[simp] lemma minor_loopyOn_iff : M ≤m loopyOn E ↔ M = loopyOn M.E ∧ M.E ⊆ E := by
  refine ⟨fun h ↦ ⟨by obtain ⟨C, D, _, _, _, rfl⟩ := h; simp, h.subset⟩, fun ⟨h, hss⟩ ↦ ?_⟩
  convert (loopyOn E).restrict_minor hss using 1
  rw [h, loopyOn_ground, loopyOn_restrict]

lemma contract_eq_loopyOn_of_spanning {C : Set α} (h : M.Spanning C) :
    M ／ C = loopyOn (M.E \ C) := by
  rw [eq_loopyOn_iff_closure, contract_ground, and_iff_left rfl, contract_closure_eq,
    empty_union, h.closure_eq]

@[simp] lemma freeOn_delete (E X : Set α) : (freeOn E) ＼ X = freeOn (E \ X) := by
  rw [← loopyOn_dual_eq, ← contract_dual_eq_dual_delete, loopyOn_contract, loopyOn_dual_eq]

@[simp] lemma freeOn_contract (E X : Set α) : (freeOn E) ／ X = freeOn (E \ X) := by
  rw [← loopyOn_dual_eq, ← delete_dual_eq_dual_contract, loopyOn_delete, loopyOn_dual_eq]

lemma restrict_indep_eq_freeOn (hI : M.Indep I) : M ↾ I = freeOn I := by
  refine ext_indep rfl (fun J _ ↦ ?_)
  simp only [restrict_ground_eq, restrict_indep_iff, freeOn_indep_iff, and_iff_right_iff_imp]
  exact hI.subset

lemma indep_iff_restrict_eq_freeOn : M.Indep I ↔ (M ↾ I = freeOn I) := by
  refine ⟨restrict_indep_eq_freeOn, fun h ↦ ?_⟩
  have h' := restrict_indep_iff (M := M) (I := I) (R := I)
  rwa [h, freeOn_indep_iff, iff_true_intro Subset.rfl, and_true, true_iff] at h'

lemma restrict_subset_loops_eq (hX : X ⊆ M.closure ∅) : M ↾ X = loopyOn X := by
  refine ext_indep rfl (fun I hI ↦ ?_)
  simp only [restrict_indep_iff, loopyOn_indep_iff]
  use fun h ↦ h.1.eq_empty_of_subset_loops (h.2.trans hX)
  rintro rfl
  simp

end Constructions

end Matroid
