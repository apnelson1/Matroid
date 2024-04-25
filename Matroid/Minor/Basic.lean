import Matroid.Rank
-- import Matroid.ForMathlib.Basic

open Set

variable {α : Type*} {M M' N : Matroid α} {e f : α} {I J R B X Y Z K : Set α}

namespace Matroid

section Delete

variable {D D₁ D₂ R : Set α}

class HasDelete (α β : Type*) where
  del : α → β → α

infixl:75 " ⧹ " => HasDelete.del

/-- The deletion `M ⧹ D` is the restriction of a matroid `M` to `M.E \ D`-/
def delete (M : Matroid α) (D : Set α) : Matroid α :=
  M ↾ (M.E \ D)

instance delSet {α : Type*} : HasDelete (Matroid α) (Set α) :=
  ⟨Matroid.delete⟩

theorem delete_eq_restrict (M : Matroid α) (D : Set α) : M ⧹ D = M ↾ (M.E \ D) := rfl

/-- Can this be an abbrev? -/
instance delElem {α : Type*} : HasDelete (Matroid α) α :=
  ⟨fun M e ↦ M.delete {e}⟩

instance delete_finite [Matroid.Finite M] : Matroid.Finite (M ⧹ D) :=
  ⟨M.ground_finite.diff D⟩

instance delete_finiteRk [FiniteRk M] : FiniteRk (M ⧹ D) :=
  restrict_finiteRk _

theorem restrict_compl (M : Matroid α) (D : Set α) : M ↾ (M.E \ D) = M ⧹ D := rfl

@[simp] theorem delete_compl (hR : R ⊆ M.E := by aesop_mat) : M ⧹ (M.E \ R) = M ↾ R := by
  rw [← restrict_compl, diff_diff_cancel_left hR]

@[simp] theorem delete_restriction (M : Matroid α) (D : Set α) : M ⧹ D ≤r M :=
  restrict_restriction _ _ (diff_subset _ _)

theorem Restriction.exists_eq_delete (hNM : N ≤r M) : ∃ D ⊆ M.E, N = M ⧹ D :=
  ⟨M.E \ N.E, diff_subset _ _, by
    obtain ⟨R, hR, rfl⟩ := hNM
    rw [delete_compl, restrict_ground_eq] ⟩

theorem restriction_iff_exists_eq_delete : N ≤r M ↔ ∃ D ⊆ M.E, N = M ⧹ D :=
  ⟨Restriction.exists_eq_delete, by rintro ⟨D, -, rfl⟩; apply delete_restriction⟩

@[simp] theorem delete_ground (M : Matroid α) (D : Set α) : (M ⧹ D).E = M.E \ D := rfl

@[aesop unsafe 10% (rule_sets := [Matroid])]
theorem delete_subset_ground (M : Matroid α) (D : Set α) : (M ⧹ D).E ⊆ M.E :=
  diff_subset _ _

@[simp] theorem deleteElem (M : Matroid α) (e : α) : M ⧹ e = M ⧹ ({e} : Set α) := rfl

theorem deleteElem_eq_self (he : e ∉ M.E) : M ⧹ e = M := by
  rwa [deleteElem, delete_eq_restrict, restrict_eq_self_iff,sdiff_eq_left,
    disjoint_singleton_right]

instance deleteElem_finite [Matroid.Finite M] {e : α} : Matroid.Finite (M ⧹ e) := by
  rw [deleteElem]; infer_instance

instance deleteElem_finiteRk [FiniteRk M] {e : α} : FiniteRk (M ⧹ e) := by
  rw [deleteElem]; infer_instance

@[simp] theorem delete_delete (M : Matroid α) (D₁ D₂ : Set α) : M ⧹ D₁ ⧹ D₂ = M ⧹ (D₁ ∪ D₂) := by
  rw [← restrict_compl, ← restrict_compl, ← restrict_compl, restrict_restrict_eq,
    restrict_ground_eq, diff_diff]
  simp [diff_subset]

theorem delete_comm (M : Matroid α) (D₁ D₂ : Set α) : M ⧹ D₁ ⧹ D₂ = M ⧹ D₂ ⧹ D₁ := by
  rw [delete_delete, union_comm, delete_delete]

theorem delete_inter_ground_eq (M : Matroid α) (D : Set α) : M ⧹ (D ∩ M.E) = M ⧹ D := by
  rw [← restrict_compl, ← restrict_compl, diff_inter_self_eq_diff]

theorem delete_eq_delete_iff : M ⧹ D₁ = M ⧹ D₂ ↔ D₁ ∩ M.E = D₂ ∩ M.E := by
  rw [← delete_inter_ground_eq, ← M.delete_inter_ground_eq D₂]
  refine' ⟨fun h ↦ _, fun h ↦ by rw [h]⟩
  apply_fun (M.E \ Matroid.E ·) at h
  simp_rw [delete_ground, diff_diff_cancel_left (inter_subset_right _ _)] at h
  assumption

@[simp] theorem delete_eq_self_iff : M ⧹ D = M ↔ Disjoint D M.E := by
  rw [← restrict_compl, restrict_eq_self_iff, sdiff_eq_left, disjoint_comm]

theorem Restriction.restrict_delete_of_disjoint (h : N ≤r M) (hX : Disjoint X N.E) :
    N ≤r (M ⧹ X) := by
  obtain ⟨D, hD, rfl⟩ := restriction_iff_exists_eq_delete.1 h
  refine restriction_iff_exists_eq_delete.2 ⟨D \ X, diff_subset_diff_left hD, ?_⟩
  rwa [delete_delete, union_diff_self, union_comm, ← delete_delete, eq_comm,
    delete_eq_self_iff]

theorem Restriction.restriction_deleteElem (h : N ≤r M) (he : e ∉ N.E) : N ≤r M ⧹ e :=
  h.restrict_delete_of_disjoint (by simpa)

@[simp] theorem delete_indep_iff : (M ⧹ D).Indep I ↔ M.Indep I ∧ Disjoint I D := by
  rw [← restrict_compl, restrict_indep_iff, subset_diff, ← and_assoc,
    and_iff_left_of_imp Indep.subset_ground]

@[simp] theorem deleteElem_indep_iff : (M ⧹ e).Indep I ↔ M.Indep I ∧ e ∉ I := by
  rw [deleteElem, delete_indep_iff, disjoint_singleton_right]

theorem Indep.of_delete (h : (M ⧹ D).Indep I) : M.Indep I :=
  (delete_indep_iff.mp h).1

theorem Indep.indep_delete_of_disjoint (h : M.Indep I) (hID : Disjoint I D) : (M ⧹ D).Indep I :=
  delete_indep_iff.mpr ⟨h, hID⟩

theorem indep_iff_delete_of_disjoint (hID : Disjoint I D) : M.Indep I ↔ (M ⧹ D).Indep I :=
  ⟨fun h ↦ h.indep_delete_of_disjoint hID, fun h ↦ h.of_delete⟩

@[simp] theorem delete_dep_iff : (M ⧹ D).Dep X ↔ M.Dep X ∧ Disjoint X D := by
  rw [dep_iff, dep_iff, delete_indep_iff, delete_ground, subset_diff]; tauto

@[simp] theorem delete_base_iff : (M ⧹ D).Base B ↔ M.Basis B (M.E \ D) := by
  rw [← restrict_compl, base_restrict_iff]

@[simp] theorem delete_basis_iff : (M ⧹ D).Basis I X ↔ M.Basis I X ∧ Disjoint X D := by
  rw [← restrict_compl, basis_restrict_iff, subset_diff, ← and_assoc,
    and_iff_left_of_imp Basis.subset_ground]

@[simp] theorem delete_basis'_iff : (M ⧹ D).Basis' I X ↔ M.Basis' I (X \ D) := by
  rw [basis'_iff_basis_inter_ground, delete_basis_iff, delete_ground, diff_eq, inter_comm M.E,
    ← inter_assoc, ← diff_eq, ← basis'_iff_basis_inter_ground, and_iff_left_iff_imp,
    inter_comm, ← inter_diff_assoc]
  exact fun _ ↦ disjoint_sdiff_left

theorem Basis.of_delete (h : (M ⧹ D).Basis I X) : M.Basis I X :=
  (delete_basis_iff.mp h).1

theorem Basis.to_delete (h : M.Basis I X) (hX : Disjoint X D) : (M ⧹ D).Basis I X := by
  rw [delete_basis_iff]; exact ⟨h, hX⟩

@[simp] theorem delete_loop_iff : (M ⧹ D).Loop e ↔ M.Loop e ∧ e ∉ D := by
  rw [← singleton_dep, delete_dep_iff, disjoint_singleton_left, singleton_dep]

@[simp] theorem delete_nonloop_iff : (M ⧹ D).Nonloop e ↔ M.Nonloop e ∧ e ∉ D := by
  rw [← indep_singleton, delete_indep_iff, disjoint_singleton_left, indep_singleton]

theorem Nonloop.of_delete (h : (M ⧹ D).Nonloop e) : M.Nonloop e :=
  (delete_nonloop_iff.1 h).1

theorem nonloop_iff_delete_of_not_mem (he : e ∉ D) : M.Nonloop e ↔ (M ⧹ D).Nonloop e :=
  ⟨fun h ↦ delete_nonloop_iff.2 ⟨h, he⟩, fun h ↦ h.of_delete⟩

@[simp] theorem delete_circuit_iff {C : Set α} :
    (M ⧹ D).Circuit C ↔ M.Circuit C ∧ Disjoint C D := by
  simp_rw [circuit_iff, delete_dep_iff, and_imp]
  rw [and_comm, ← and_assoc, and_congr_left_iff, and_comm, and_congr_right_iff]
  exact fun hdj _↦ ⟨fun h I hId hIC ↦ h hId (disjoint_of_subset_left hIC hdj) hIC,
    fun h I hI _ hIC ↦ h hI hIC⟩

theorem Circuit.of_delete {C : Set α} (h : (M ⧹ D).Circuit C) : M.Circuit C :=
  (delete_circuit_iff.1 h).1

theorem circuit_iff_delete_of_disjoint {C : Set α} (hCD : Disjoint C D) :
    M.Circuit C ↔ (M ⧹ D).Circuit C :=
  ⟨fun h ↦ delete_circuit_iff.2 ⟨h, hCD⟩, fun h ↦ h.of_delete⟩

@[simp] theorem delete_cl_eq (M : Matroid α) (D X : Set α) : (M ⧹ D).cl X = M.cl (X \ D) \ D := by
  rw [← restrict_compl, restrict_cl_eq', sdiff_sdiff_self, bot_eq_empty, union_empty,
    diff_eq, inter_comm M.E, ← inter_assoc X, ← diff_eq, cl_inter_ground,
    ← inter_assoc, ← diff_eq, inter_eq_left]
  exact (diff_subset _ _).trans (M.cl_subset_ground _)

theorem delete_loops_eq (M : Matroid α) (D : Set α) : (M ⧹ D).cl ∅ = M.cl ∅ \ D := by
  simp

@[simp] theorem delete_empty (M : Matroid α) : M ⧹ (∅ : Set α) = M := by
  rw [delete_eq_self_iff]; exact empty_disjoint _

theorem delete_delete_diff (M : Matroid α) (D₁ D₂ : Set α) : M ⧹ D₁ ⧹ D₂ = M ⧹ D₁ ⧹ (D₂ \ D₁) :=
  by simp

instance delete_finitary (M : Matroid α) [Finitary M] (D : Set α) : Finitary (M ⧹ D) := by
  change Finitary (M ↾ (M.E \ D)); infer_instance

instance deleteElem_finitary (M : Matroid α) [Finitary M] (e : α) : Finitary (M ⧹ e) := by
  rw [deleteElem]; infer_instance

theorem removeLoops_eq_delete (M : Matroid α) : M.removeLoops = M ⧹ M.cl ∅ := by
  rw [← restrict_compl, removeLoops]
  convert rfl using 2
  simp [Set.ext_iff, mem_setOf, Nonloop, Loop, mem_diff, and_comm]

end Delete

section Contract

variable {C C₁ C₂ : Set α}

class HasContract (α β : Type*) where
  con : α → β → α

infixl:75 " ⧸ " => HasContract.con

/-- The contraction `M ⧸ C` is the matroid on `M.E \ C` whose bases are the sets `B \ I` where `B`
  is a base for `M` containing a base `I` for `C`. It is also equal to the dual of `M✶ ⧹ C`, and
  is defined this way so we don't have to give a separate proof that it is actually a matroid. -/
def contract (M : Matroid α) (C : Set α) : Matroid α := (M✶ ⧹ C)✶

instance conSet {α : Type*} : HasContract (Matroid α) (Set α) :=
  ⟨Matroid.contract⟩

instance conElem {α : Type*} : HasContract (Matroid α) α :=
  ⟨fun M e ↦ M.contract {e}⟩

@[simp] theorem dual_delete_dual_eq_contract (M : Matroid α) (X : Set α) : (M✶ ⧹ X)✶ = M ⧸ X :=
  rfl

@[simp] theorem dual_contract_dual_eq_delete (M : Matroid α) (X : Set α) : (M✶ ⧸ X)✶ = M ⧹ X := by
  rw [← dual_delete_dual_eq_contract, dual_dual, dual_dual]

@[simp] theorem contract_dual_eq_dual_delete (M : Matroid α) (X : Set α) : (M ⧸ X)✶ = M✶ ⧹ X := by
  rw [← dual_delete_dual_eq_contract, dual_dual]

@[simp] theorem delete_dual_eq_dual_contract (M : Matroid α) (X : Set α) : (M ⧹ X)✶ = M✶ ⧸ X := by
  rw [← dual_delete_dual_eq_contract, dual_dual]

@[simp] theorem contract_ground (M : Matroid α) (C : Set α) : (M ⧸ C).E = M.E \ C := rfl

instance contract_finite [Matroid.Finite M] : Matroid.Finite (M ⧸ C) := by
  rw [← dual_delete_dual_eq_contract]; infer_instance

@[aesop unsafe 10% (rule_sets := [Matroid])]
theorem contract_ground_subset_ground (M : Matroid α) (C : Set α) : (M ⧸ C).E ⊆ M.E :=
  (M.contract_ground C).trans_subset (diff_subset _ _)

@[simp] theorem contract_elem (M : Matroid α) (e : α) : M ⧸ e = M ⧸ ({e} : Set α) :=
  rfl

@[simp] theorem contract_contract (M : Matroid α) (C₁ C₂ : Set α) :
    M ⧸ C₁ ⧸ C₂ = M ⧸ (C₁ ∪ C₂) := by
  rw [eq_comm, ← dual_delete_dual_eq_contract, ← delete_delete, ← dual_contract_dual_eq_delete, ←
    dual_contract_dual_eq_delete, dual_dual, dual_dual, dual_dual]

theorem contract_comm (M : Matroid α) (C₁ C₂ : Set α) : M ⧸ C₁ ⧸ C₂ = M ⧸ C₂ ⧸ C₁ := by
  rw [contract_contract, union_comm, contract_contract]

theorem contract_eq_self_iff : M ⧸ C = M ↔ Disjoint C M.E := by
  rw [← dual_delete_dual_eq_contract, ← dual_inj, dual_dual, delete_eq_self_iff, dual_ground]

@[simp] theorem contract_empty (M : Matroid α) : M ⧸ (∅ : Set α) = M := by
  rw [← dual_delete_dual_eq_contract, delete_empty, dual_dual]

theorem contract_contract_diff (M : Matroid α) (C₁ C₂ : Set α) :
    M ⧸ C₁ ⧸ C₂ = M ⧸ C₁ ⧸ (C₂ \ C₁) := by
  simp

theorem contract_eq_contract_iff : M ⧸ C₁ = M ⧸ C₂ ↔ C₁ ∩ M.E = C₂ ∩ M.E := by
  rw [← dual_delete_dual_eq_contract, ← dual_delete_dual_eq_contract, dual_inj,
    delete_eq_delete_iff, dual_ground]

@[simp] theorem contract_inter_ground_eq (M : Matroid α) (C : Set α) : M ⧸ (C ∩ M.E) = M ⧸ C := by
  rw [← dual_delete_dual_eq_contract, (show M.E = M✶.E from rfl), delete_inter_ground_eq]; rfl

theorem coindep_contract_iff : (M ⧸ C).Coindep X ↔ M.Coindep X ∧ Disjoint X C := by
  rw [coindep_def, contract_dual_eq_dual_delete, delete_indep_iff, ← coindep_def]

theorem Coindep.coindep_contract_of_disjoint (hX : M.Coindep X) (hXC : Disjoint X C) :
    (M ⧸ C).Coindep X :=
  coindep_contract_iff.mpr ⟨hX, hXC⟩

theorem Indep.contract_base_iff (hI : M.Indep I) :
    (M ⧸ I).Base B ↔ M.Base (B ∪ I) ∧ Disjoint B I := by
  have hIE := hI.subset_ground
  rw [← dual_dual M, ← coindep_def, coindep_iff_exists] at hI
  obtain ⟨B₀, hB₀, hfk⟩ := hI
  rw [← dual_dual M, ← dual_delete_dual_eq_contract, dual_base_iff', dual_base_iff',
    delete_base_iff, dual_dual, delete_ground, diff_diff, union_comm, union_subset_iff,
    subset_diff, ← and_assoc, and_congr_left_iff, dual_ground, and_iff_left hIE, and_congr_left_iff]
  refine' fun _ _ ↦
    ⟨fun h ↦ h.base_of_base_subset hB₀ (subset_diff.mpr ⟨hB₀.subset_ground, _⟩), fun hB ↦
      hB.basis_of_subset (diff_subset _ _) (diff_subset_diff_right (subset_union_right _ _))⟩
  exact disjoint_of_subset_left hfk disjoint_sdiff_left

theorem Indep.contract_indep_iff (hI : M.Indep I) :
    (M ⧸ I).Indep J ↔ Disjoint J I ∧ M.Indep (J ∪ I) := by
  simp_rw [indep_iff_subset_base, hI.contract_base_iff, union_subset_iff]
  exact ⟨fun ⟨B, ⟨hBI, hdj⟩, hJB⟩ ↦
    ⟨disjoint_of_subset_left hJB hdj, _, hBI, hJB.trans (subset_union_left _ _),
      subset_union_right _ _⟩,
    fun ⟨hdj, B, hB, hJB, hIB⟩ ↦ ⟨B \ I,⟨by simpa [union_eq_self_of_subset_right hIB],
      disjoint_sdiff_left⟩, subset_diff.2 ⟨hJB, hdj⟩ ⟩⟩

theorem Indep.union_indep_iff_contract_indep (hI : M.Indep I) :
    M.Indep (I ∪ J) ↔ (M ⧸ I).Indep (J \ I) := by
  rw [hI.contract_indep_iff, and_iff_right disjoint_sdiff_left, diff_union_self, union_comm]

theorem Indep.diff_indep_contract_of_subset (hJ : M.Indep J) (hIJ : I ⊆ J) :
    (M ⧸ I).Indep (J \ I) := by
  rwa [← (hJ.subset hIJ).union_indep_iff_contract_indep, union_eq_self_of_subset_left hIJ]

theorem Indep.contract_dep_iff (hI : M.Indep I) :
    (M ⧸ I).Dep J ↔ Disjoint J I ∧ M.Dep (J ∪ I) := by
  rw [dep_iff, hI.contract_indep_iff, dep_iff, contract_ground, subset_diff, disjoint_comm,
    union_subset_iff, and_iff_left hI.subset_ground]
  tauto

theorem Indep.union_contract_basis_union_of_basis (hI : M.Indep I) (hB : (M ⧸ I).Basis J X) :
    M.Basis (J ∪ I) (X ∪ I) := by
  have hi := hB.indep
  rw [hI.contract_indep_iff] at hi
  refine' hi.2.basis_of_maximal_subset (union_subset_union_left _ hB.subset) _ _
  · intro K hK hJIK hKXI
    rw [union_subset_iff] at hJIK
    have hK' : (M ⧸ I).Indep (K \ I) := hK.diff_indep_contract_of_subset hJIK.2
    have hm := hB.eq_of_subset_indep hK'
    rw [subset_diff, and_iff_left hi.1, diff_subset_iff, union_comm, imp_iff_right hKXI,
      imp_iff_right hJIK.1] at hm
    simp [hm]
  exact union_subset (hB.subset_ground.trans (contract_ground_subset_ground _ _)) hI.subset_ground

theorem Basis.contract_basis_union_union (h : M.Basis (J ∪ I) (X ∪ I)) (hdj : Disjoint (J ∪ X) I) :
    (M ⧸ I).Basis J X := by
  rw [disjoint_union_left] at hdj
  have hI := h.indep.subset (subset_union_right _ _)
  simp_rw [Basis, mem_maximals_setOf_iff, hI.contract_indep_iff, and_iff_right hdj.1,
    and_iff_right h.indep, contract_ground, subset_diff, and_iff_left hdj.2,
    and_iff_left ((subset_union_left _ _).trans h.subset_ground), and_imp,
    and_iff_right
      (Disjoint.subset_left_of_subset_union ((subset_union_left _ _).trans h.subset) hdj.1)]
  intro Y hYI hYi hYX hJY
  have hu :=
    h.eq_of_subset_indep hYi (union_subset_union_left _ hJY) (union_subset_union_left _ hYX)
  apply_fun fun x : Set α ↦ x \ I at hu
  simp_rw [union_diff_right, hdj.1.sdiff_eq_left, hYI.sdiff_eq_left] at hu
  exact hu

theorem contract_eq_delete_of_subset_coloops (hX : X ⊆ M✶.cl ∅) : M ⧸ X = M ⧹ X := by
  refine' eq_of_indep_iff_indep_forall rfl fun I _ ↦ _
  rw [(indep_of_subset_coloops hX).contract_indep_iff, delete_indep_iff, and_comm,
    union_indep_iff_indep_of_subset_coloops hX]

theorem contract_eq_delete_of_subset_loops (hX : X ⊆ M.cl ∅) : M ⧸ X = M ⧹ X := by
  rw [← dual_inj, contract_dual_eq_dual_delete, delete_dual_eq_dual_contract, eq_comm,
    contract_eq_delete_of_subset_coloops]
  rwa [dual_dual]

theorem Basis.contract_eq_contract_delete (hI : M.Basis I X) : M ⧸ X = M ⧸ I ⧹ (X \ I) := by
  nth_rw 1 [← diff_union_of_subset hI.subset]
  rw [union_comm, ← contract_contract]
  refine' contract_eq_delete_of_subset_loops fun e he ↦ _
  rw [← loop_iff_mem_cl_empty, ← singleton_dep, hI.indep.contract_dep_iff,
    disjoint_singleton_left, and_iff_right he.2, singleton_union,
    ← hI.indep.mem_cl_iff_of_not_mem he.2]
  exact hI.subset_cl he.1

theorem Basis'.contract_eq_contract_delete (hI : M.Basis' I X) : M ⧸ X = M ⧸ I ⧹ (X \ I) := by
  rw [← contract_inter_ground_eq, hI.basis_inter_ground.contract_eq_contract_delete, eq_comm,
    ← delete_inter_ground_eq, contract_ground, diff_eq, diff_eq, ← inter_inter_distrib_right,
    ← diff_eq]

theorem Basis'.contract_indep_iff (hI : M.Basis' I X) :
    (M ⧸ X).Indep J ↔ M.Indep (J ∪ I) ∧ Disjoint X J := by
  rw [hI.contract_eq_contract_delete, delete_indep_iff, hI.indep.contract_indep_iff,
    and_comm, ← and_assoc, ← disjoint_union_right, diff_union_self,
    union_eq_self_of_subset_right hI.subset, and_comm, disjoint_comm]

theorem Basis.contract_indep_iff (hI : M.Basis I X) :
    (M ⧸ X).Indep J ↔ M.Indep (J ∪ I) ∧ Disjoint X J :=
  hI.basis'.contract_indep_iff

theorem contract_cl_eq_contract_delete (M : Matroid α) (C : Set α) :
    M ⧸ M.cl C = M ⧸ C ⧹ (M.cl C \ C) := by
  obtain ⟨I, hI⟩ := M.exists_basis_inter_ground_basis_cl C
  rw [hI.2.contract_eq_contract_delete, ← M.contract_inter_ground_eq C,
    hI.1.contract_eq_contract_delete, delete_delete]
  convert rfl using 2
  rw [union_comm, diff_eq (t := I), union_inter_distrib_left, union_inter_distrib_left,
    diff_union_self, union_eq_self_of_subset_left ((diff_subset _ _).trans (M.cl_subset_ground _)),
      union_inter_distrib_right, diff_eq, inter_eq_self_of_subset_left (M.cl_subset_ground _),
      ← cl_inter_ground, union_eq_self_of_subset_right (M.subset_cl (C ∩ M.E)),
      inter_union_distrib_left, ← inter_assoc, inter_self, ← inter_union_distrib_left,
      ← compl_inter, ← diff_eq,
      inter_eq_self_of_subset_right (hI.1.subset.trans (inter_subset_left _ _))]

theorem exists_eq_contract_indep_delete (M : Matroid α) (C : Set α) :
    ∃ I D : Set α, M.Basis I (C ∩ M.E) ∧ D ⊆ (M ⧸ I).E ∧ D ⊆ C ∧ M ⧸ C = M ⧸ I ⧹ D := by
  obtain ⟨I, hI⟩ := M.exists_basis (C ∩ M.E)
  use I, C \ I ∩ M.E, hI
  rw [contract_ground, and_iff_right ((inter_subset_left _ _).trans (diff_subset _ _)), diff_eq,
    diff_eq, inter_right_comm, inter_assoc, and_iff_right (inter_subset_right _ _),
    ← contract_inter_ground_eq, hI.contract_eq_contract_delete, diff_eq, inter_assoc]

theorem Indep.of_contract (hI : (M ⧸ C).Indep I) : M.Indep I := by
  obtain ⟨J, R, hJ, -, -, hM⟩ := M.exists_eq_contract_indep_delete C
  rw [hM, delete_indep_iff, hJ.indep.contract_indep_iff] at hI
  exact hI.1.2.subset (subset_union_left _ _)

instance contract_finiteRk [FiniteRk M] : FiniteRk (M ⧸ C) := by
  obtain ⟨B, hB⟩ := (M ⧸ C).exists_base
  refine ⟨B, hB, hB.indep.of_contract.finite⟩

instance contract_finitary [Finitary M] : Finitary (M ⧸ C) := by
  obtain ⟨J, D, hJ, -, -, hM⟩ := M.exists_eq_contract_indep_delete C
  rw [hM]
  suffices Finitary (M ⧸ J) by infer_instance
  refine ⟨fun I hI ↦ ?_⟩
  simp_rw [hJ.indep.contract_indep_iff] at hI ⊢
  simp_rw [disjoint_iff_forall_ne]
  refine ⟨fun x hx y hy ↦ ?_, ?_⟩
  · rintro rfl
    specialize hI {x} (singleton_subset_iff.2 hx) (finite_singleton _)
    simp only [disjoint_singleton_left, singleton_union] at hI
    exact hI.1 hy
  apply indep_of_forall_finite_subset_indep _ (fun K hK hKfin ↦ ?_)
  specialize hI (K ∩ I) (inter_subset_right _ _) (hKfin.subset (inter_subset_left _ _))
  refine hI.2.subset <| (subset_inter Subset.rfl hK).trans ?_
  rw [inter_union_distrib_left]
  exact union_subset_union Subset.rfl (inter_subset_right _ _)

instance contractElem_finiteRk [FiniteRk M] {e : α} : FiniteRk (M ⧸ e) := by
  rw [contract_elem]; infer_instance

instance contractElem_finitary [Finitary M] {e : α} : Finitary (M ⧸ e) := by
  rw [contract_elem]; infer_instance

@[simp] theorem contract_loop_iff_mem_cl : (M ⧸ C).Loop e ↔ e ∈ M.cl C \ C := by
  obtain ⟨I, D, hI, -, -, hM⟩ := M.exists_eq_contract_indep_delete C
  rw [hM, delete_loop_iff, ← singleton_dep, hI.indep.contract_dep_iff, disjoint_singleton_left,
    singleton_union, hI.indep.insert_dep_iff, mem_diff, ← M.cl_inter_ground C, hI.cl_eq_cl,
    and_comm (a := e ∉ I), and_self_right, ← mem_diff, ← mem_diff, diff_diff]
  apply_fun Matroid.E at hM
  rw [delete_ground, contract_ground, contract_ground, diff_diff, diff_eq_diff_iff_inter_eq_inter,
    inter_comm, inter_comm M.E] at hM
  exact
    ⟨fun h ↦ ⟨h.1, fun heC ↦ h.2 (hM.subset ⟨heC, M.cl_subset_ground _ h.1⟩).1⟩, fun h ↦
      ⟨h.1, fun h' ↦ h.2 (hM.symm.subset ⟨h', M.cl_subset_ground _ h.1⟩).1⟩⟩

theorem contract_loops_eq : (M ⧸ C).cl ∅ = M.cl C \ C := by
  simp [Set.ext_iff, ← loop_iff_mem_cl_empty, contract_loop_iff_mem_cl]

@[simp] theorem contract_cl_eq (M : Matroid α) (C X : Set α) :
    (M ⧸ C).cl X = M.cl (X ∪ C) \ C := by
  ext e
  by_cases heX : e ∈ X
  · by_cases he : e ∈ (M ⧸ C).E
    · refine' iff_of_true (mem_cl_of_mem' _ heX) _
      rw [contract_ground] at he
      exact ⟨mem_cl_of_mem' _ (Or.inl heX) he.1, he.2⟩
    refine' iff_of_false (he ∘ fun h ↦ cl_subset_ground _ _ h) (he ∘ fun h ↦ _)
    rw [contract_ground]
    exact ⟨M.cl_subset_ground _ h.1, h.2⟩
  suffices h' : e ∈ (M ⧸ C).cl X \ X ↔ e ∈ M.cl (X ∪ C) \ (X ∪ C) by
    rwa [mem_diff, and_iff_left heX, mem_diff, mem_union, or_iff_right heX, ← mem_diff] at h'
  rw [← contract_loop_iff_mem_cl, ← contract_loop_iff_mem_cl, contract_contract, union_comm]

theorem Circuit.contract_dep (hK : M.Circuit K) (hCK : Disjoint C K) : (M ⧸ C).Dep K := by
  obtain ⟨I, hI⟩ := M.exists_basis (C ∩ M.E)
  rw [← contract_inter_ground_eq, Dep, hI.contract_indep_iff,
    and_iff_left (hCK.mono_left (inter_subset_left _ _)), contract_ground, subset_diff,
    and_iff_left (hCK.symm.mono_right (inter_subset_left _ _)), and_iff_left hK.subset_ground]
  exact fun hi ↦ hK.dep.not_indep (hi.subset (subset_union_left _ _))

theorem Dep.of_contract (h : (M ⧸ C).Dep X) (hC : C ⊆ M.E := by aesop_mat) : M.Dep (C ∪ X) := by
  rw [Dep, and_iff_left (union_subset hC (h.subset_ground.trans (diff_subset _ _)))]
  intro hi
  rw [Dep, (hi.subset (subset_union_left _ _)).contract_indep_iff, union_comm,
    and_iff_left hi] at h
  exact h.1 (subset_diff.1 h.2).2

theorem Basis.diff_subset_loops_contract (hIX : M.Basis I X) : X \ I ⊆ (M ⧸ I).cl ∅ := by
  rw [diff_subset_iff, contract_loops_eq, union_diff_self,
    union_eq_self_of_subset_left (M.subset_cl I)]
  exact hIX.subset_cl

theorem contract_spanning_iff' (M : Matroid α) (C X : Set α) :
    (M ⧸ C).Spanning X ↔ M.Spanning (X ∪ (C ∩ M.E)) ∧ Disjoint X C := by
  simp_rw [Spanning, contract_cl_eq, contract_ground, subset_diff, union_subset_iff,
    and_iff_left (inter_subset_right _ _), ← and_assoc, and_congr_left_iff,
    subset_antisymm_iff, subset_diff, diff_subset_iff, and_iff_left disjoint_sdiff_left,
    and_iff_right (M.cl_subset_ground _ ),
    and_iff_right (subset_union_of_subset_right (M.cl_subset_ground _) C)]
  rw [← inter_eq_left (s := M.E), inter_union_distrib_left,
    inter_eq_self_of_subset_right (M.cl_subset_ground _), subset_antisymm_iff, union_subset_iff,
    and_iff_right (inter_subset_left _ _), union_eq_self_of_subset_left (s := M.E ∩ C),
    and_iff_right (M.cl_subset_ground _), Iff.comm, ← cl_union_cl_right_eq,cl_inter_ground,
    cl_union_cl_right_eq]
  · exact fun _ _ ↦ Iff.rfl
  exact (M.subset_cl _).trans
    (M.cl_subset_cl ((inter_subset_right _ _).trans (subset_union_right _ _)))

theorem contract_spanning_iff (hC : C ⊆ M.E := by aesop_mat) :
    (M ⧸ C).Spanning X ↔ M.Spanning (X ∪ C) ∧ Disjoint X C := by
  rw [contract_spanning_iff', inter_eq_self_of_subset_left hC]

theorem Nonloop.of_contract (h : (M ⧸ C).Nonloop e) : M.Nonloop e := by
  rw [← indep_singleton] at h ⊢
  exact h.of_contract

@[simp] theorem contract_nonloop_iff : (M ⧸ C).Nonloop e ↔ e ∈ M.E \ M.cl C := by
  rw [nonloop_iff_mem_compl_loops, contract_ground, contract_loops_eq]
  refine ⟨fun ⟨he,heC⟩ ↦ ⟨he.1, fun h ↦ heC ⟨h, he.2⟩⟩,
    fun h ↦ ⟨⟨h.1, fun heC ↦ h.2 ?_⟩, fun h' ↦ h.2 h'.1⟩⟩
  rw [← cl_inter_ground]
  exact (M.subset_cl (C ∩ M.E)) ⟨heC, h.1⟩

end Contract

section Minor

variable {M₀ M₁ M₂ : Matroid α}

theorem contract_delete_diff (M : Matroid α) (C D : Set α) : M ⧸ C ⧹ D = M ⧸ C ⧹ (D \ C) := by
  rw [delete_eq_delete_iff, contract_ground, diff_eq, diff_eq, ← inter_inter_distrib_right,
    inter_assoc]

theorem contract_restrict_eq_restrict_contract (M : Matroid α) (C R : Set α) (h : Disjoint C R) :
    (M ⧸ C) ↾ R = (M ↾ (R ∪ C)) ⧸ C := by
  refine eq_of_indep_iff_indep_forall (by simp [h.sdiff_eq_right]) (fun I _ ↦ ?_)
  obtain ⟨J, hJ⟩ := (M ↾ (R ∪ C)).exists_basis' C
  have hJ' : M.Basis' J C := by
    have := (basis'_restrict_iff.1 hJ).1
    rwa [inter_eq_self_of_subset_left (subset_union_right _ _)] at this
  rw [restrict_indep_iff, hJ.contract_indep_iff, hJ'.contract_indep_iff, restrict_indep_iff,
    union_subset_iff, and_iff_left (hJ.subset.trans (subset_union_right _ _)), union_comm R C,
    ← diff_subset_iff, and_assoc, and_assoc, and_congr_right_iff, and_comm, and_congr_left_iff]
  intro _ hd
  rw [hd.sdiff_eq_right]

/- TODO : Simplify this proof using the lemma above-/
theorem contract_delete_comm (M : Matroid α) {C D : Set α} (hCD : Disjoint C D) :
    M ⧸ C ⧹ D = M ⧹ D ⧸ C := by
  refine eq_of_indep_iff_indep_forall (by simp [diff_diff_comm]) (fun I hI ↦ ?_)
  rw [delete_ground, contract_ground, subset_diff, subset_diff] at hI
  simp only [delete_ground, contract_ground, delete_indep_iff, and_iff_left hI.2]
  obtain ⟨J, hJ⟩ := (M ⧹ D).exists_basis' C;  have hJ' := hJ
  rw [← restrict_compl, basis'_restrict_iff, subset_diff, diff_eq, inter_comm M.E, ← inter_assoc,
    ← diff_eq, sdiff_eq_left.2 hCD] at hJ'
  rw [hJ.contract_eq_contract_delete, delete_indep_iff, hJ.indep.contract_indep_iff,
    delete_indep_iff, ← contract_inter_ground_eq, hJ'.1.contract_eq_contract_delete,
    delete_indep_iff,  hJ'.1.indep.contract_indep_iff, disjoint_union_left, and_iff_right hI.2,
    and_iff_left (disjoint_of_subset_right (diff_subset _ _) hI.1.2), and_iff_left hJ'.2.2,
    and_iff_left
    (disjoint_of_subset_right ((diff_subset _ _).trans (inter_subset_left _ _)) hI.1.2)]

theorem contract_delete_comm' (M : Matroid α) (C D : Set α) : M ⧸ C ⧹ D = M ⧹ (D \ C) ⧸ C := by
  rw [contract_delete_diff, contract_delete_comm _ disjoint_sdiff_right]

theorem delete_contract_diff (M : Matroid α) (D C : Set α) : M ⧹ D ⧸ C = M ⧹ D ⧸ (C \ D) := by
  rw [contract_eq_contract_iff, delete_ground, diff_inter_diff_right, diff_eq, diff_eq, inter_assoc]

theorem delete_contract_comm' (M : Matroid α) (D C : Set α) : M ⧹ D ⧸ C = M ⧸ (C \ D) ⧹ D := by
  rw [delete_contract_diff, ← contract_delete_comm _ disjoint_sdiff_left]

theorem contract_delete_contract' (M : Matroid α) (C D C' : Set α) :
    M ⧸ C ⧹ D ⧸ C' = M ⧸ (C ∪ C' \ D) ⧹ D := by
  rw [delete_contract_diff, ← contract_delete_comm _ disjoint_sdiff_left, contract_contract]

theorem contract_delete_contract (M : Matroid α) (C D C' : Set α) (h : Disjoint C' D) :
    M ⧸ C ⧹ D ⧸ C' = M ⧸ (C ∪ C') ⧹ D := by rw [contract_delete_contract', sdiff_eq_left.mpr h]

theorem contract_delete_contract_delete' (M : Matroid α) (C D C' D' : Set α) :
    M ⧸ C ⧹ D ⧸ C' ⧹ D' = M ⧸ (C ∪ C' \ D) ⧹ (D ∪ D') := by
  rw [contract_delete_contract', delete_delete]

theorem contract_delete_contract_delete (M : Matroid α) (C D C' D' : Set α) (h : Disjoint C' D) :
    M ⧸ C ⧹ D ⧸ C' ⧹ D' = M ⧸ (C ∪ C') ⧹ (D ∪ D') := by
  rw [contract_delete_contract_delete', sdiff_eq_left.mpr h]

theorem delete_contract_delete' (M : Matroid α) (D C D' : Set α) :
    M ⧹ D ⧸ C ⧹ D' = M ⧸ (C \ D) ⧹ (D ∪ D') := by
  rw [delete_contract_comm', delete_delete]

theorem delete_contract_delete (M : Matroid α) (D C D' : Set α) (h : Disjoint C D) :
    M ⧹ D ⧸ C ⧹ D' = M ⧸ C ⧹ (D ∪ D') := by
  rw [delete_contract_delete', sdiff_eq_left.mpr h]

/- `N` is a minor of `M` if `N = M ⧸ C ⧹ D` for disjoint sets `C,D ⊆ M.E`-/
def Minor (N M : Matroid α) : Prop :=
  ∃ C D, C ⊆ M.E ∧ D ⊆ M.E ∧ Disjoint C D ∧ N = M ⧸ C ⧹ D

def StrictMinor (N M : Matroid α) : Prop :=
  Minor N M ∧ ¬Minor M N

infixl:50 " ≤m " => Matroid.Minor
infixl:50 " <m " => Matroid.StrictMinor

theorem contract_delete_minor (M : Matroid α) (C D : Set α) : M ⧸ C ⧹ D ≤m M := by
  rw [contract_delete_diff, ← contract_inter_ground_eq, ← delete_inter_ground_eq,
    contract_ground, diff_inter_self_eq_diff, diff_inter_diff_right, inter_diff_right_comm]
  refine ⟨_,_, inter_subset_right _ _, inter_subset_right _ _, ?_, rfl⟩
  exact disjoint_of_subset (inter_subset_left C M.E) (inter_subset_left _ M.E) disjoint_sdiff_right

theorem minor_def : N ≤m M ↔ ∃ C D, C ⊆ M.E ∧ D ⊆ M.E ∧ Disjoint C D ∧ N = M ⧸ C ⧹ D := Iff.rfl

theorem minor_iff_exists_contract_delete : N ≤m M ↔ ∃ C D : Set α, N = M ⧸ C ⧹ D :=
  ⟨fun ⟨C, D, h⟩ ↦ ⟨_,_,h.2.2.2⟩, fun ⟨C, D, h⟩ ↦ by rw [h]; apply contract_delete_minor⟩

theorem Indep.of_minor (hI : N.Indep I) (hNM : N ≤m M) : M.Indep I := by
  obtain ⟨C,D, rfl⟩ := minor_iff_exists_contract_delete.1 hNM
  exact hI.of_delete.of_contract

theorem Nonloop.of_minor (h : N.Nonloop e) (hNM : N ≤m M) : M.Nonloop e := by
  obtain ⟨C, D, rfl⟩ := minor_iff_exists_contract_delete.1 hNM
  exact h.of_delete.of_contract

theorem Loop.minor (he : M.Loop e) (heN : e ∈ N.E) (hNM : N ≤m M) : N.Loop e := by
  rw [← not_nonloop_iff]
  exact fun hnl ↦ he.not_nonloop <| hnl.of_minor hNM

lemma Minor.eq_of_ground_subset (h : N ≤m M) (hE : M.E ⊆ N.E) : M = N := by
  obtain ⟨C, D, -, -, -, rfl⟩ := h
  rw [delete_ground, contract_ground, subset_diff, subset_diff] at hE
  rw [← contract_inter_ground_eq, hE.1.2.symm.inter_eq, contract_empty, ← delete_inter_ground_eq,
    hE.2.symm.inter_eq, delete_empty]

lemma Minor.subset (h : N ≤m M) : N.E ⊆ M.E := by
  obtain ⟨C, D, -, -, -, rfl⟩ := h; exact (diff_subset _ _).trans (diff_subset _ _)

theorem Minor.refl {M : Matroid α} : M ≤m M :=
  minor_iff_exists_contract_delete.2 ⟨∅, ∅, by simp⟩

theorem Minor.trans {M₁ M₂ M₃ : Matroid α} (h : M₁ ≤m M₂) (h' : M₂ ≤m M₃) : M₁ ≤m M₃ := by
  obtain ⟨C₁, D₁, -, -, -, rfl⟩ := h
  obtain ⟨C₂, D₂, -, -, -, rfl⟩ := h'
  rw [contract_delete_contract_delete']
  apply contract_delete_minor

theorem Minor.antisymm (h : N ≤m M) (h' : M ≤m N) : N = M :=
  h'.eq_of_ground_subset h.subset

/-- The minor order is a `PartialOrder` on `Matroid α`. We prefer the spelling `M ≤m M'`
  to `M ≤ M'` for the dot notation. -/
instance (α : Type*) : PartialOrder (Matroid α) where
  le M M' := M ≤m M'
  lt M M' := M <m M'
  le_refl M := Minor.refl
  le_trans _ _ _ h h' := Minor.trans h h'
  le_antisymm _ _ h h' := Minor.antisymm h h'

theorem Minor.finite (h : N ≤m M) [M.Finite] : N.Finite :=
  ⟨M.ground_finite.subset h.subset⟩

theorem Minor.finiteRk (h : N ≤m M) [FiniteRk M] : FiniteRk N := by
  obtain ⟨C, D, rfl⟩ := minor_iff_exists_contract_delete.1 h
  infer_instance

theorem Minor.finitary (h : N ≤m M) [Finitary M] : Finitary N := by
  obtain ⟨C, D, rfl⟩ := minor_iff_exists_contract_delete.1 h
  infer_instance

@[simp] protected theorem le_iff (M M' : Matroid α) : M ≤ M' ↔ M ≤m M' := Iff.rfl

@[simp] protected theorem lt_iff (M M' : Matroid α) : M < M' ↔ M <m M' := Iff.rfl

theorem StrictMinor.minor (h : N <m M) : N ≤m M :=
  le_of_lt h

theorem StrictMinor.not_minor (h : N <m M) : ¬ (M ≤m N) :=
  not_le_of_lt h

theorem strictMinor_iff_minor_ne : N <m M ↔ N ≤m M ∧ N ≠ M :=
  lt_iff_le_and_ne (α := Matroid α)

theorem StrictMinor.ne (h : N <m M) : N ≠ M :=
  LT.lt.ne h

theorem strictMinor_irrefl (M : Matroid α) : ¬ (M <m M) :=
  lt_irrefl M

theorem StrictMinor.ssubset (h : N <m M) : N.E ⊂ M.E :=
  h.minor.subset.ssubset_of_ne (fun hE ↦ h.ne (h.minor.eq_of_ground_subset hE.symm.subset).symm)

theorem strictMinor_iff_minor_ssubset : N <m M ↔ N ≤m M ∧ N.E ⊂ M.E :=
  ⟨fun h ↦ ⟨h.minor, h.ssubset⟩, fun ⟨h, hss⟩ ↦ ⟨h, fun h' ↦ hss.ne <| by rw [h'.antisymm h]⟩⟩

theorem StrictMinor.trans_minor (h : N <m M) (h' : M ≤m M') : N <m M' :=
  lt_of_lt_of_le h h'

theorem Minor.trans_strictMinor (h : N ≤m M) (h' : M <m M') : N <m M' :=
  lt_of_le_of_lt h h'

theorem StrictMinor.trans (h : N <m M) (h' : M <m M') : N <m M' :=
  lt_trans h h'

theorem strictMinor_iff_exists_eq_contract_delete :
    N <m M ↔ ∃ C D, C ⊆ M.E ∧ D ⊆ M.E ∧ Disjoint C D ∧ (C ∪ D).Nonempty ∧ N = M ⧸ C ⧹ D := by
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
    and_iff_right (diff_subset _ _)]
  exact fun hss ↦ (hss ((union_subset hC hD) he)).2 he

theorem contract_minor (M : Matroid α) (C : Set α) : M ⧸ C ≤m M := by
  rw [← (M ⧸ C).delete_empty]; apply contract_delete_minor

theorem contract_minor_of_subset (M : Matroid α) {C C' : Set α} (hCC' : C ⊆ C') :
    M ⧸ C' ≤m M ⧸ C := by
  rw [← diff_union_of_subset hCC', union_comm, ← contract_contract]
  apply contract_minor

theorem contract_minor_of_mem (M : Matroid α) {C : Set α} (he : e ∈ C) :
    M ⧸ C ≤m M ⧸ e :=
  M.contract_minor_of_subset (singleton_subset_iff.2 he)

theorem delete_minor (M : Matroid α) (D : Set α) : M ⧹ D ≤m M := by
  nth_rw 1 [← M.contract_empty]; apply contract_delete_minor

theorem restrict_minor (M : Matroid α) (hR : R ⊆ M.E := by aesop_mat) : (M ↾ R) ≤m M := by
  rw [← delete_compl]; apply delete_minor

theorem Restriction.minor (h : N ≤r M) : N ≤m M := by
  rw [← h.eq_restrict, ← delete_compl h.subset]; apply delete_minor

theorem StrictRestriction.strictMinor (h : N <r M) : N <m M :=
  ⟨h.restriction.minor, fun h' ↦ h.ssubset.not_subset h'.subset⟩

theorem restrict_strictMinor (hR : R ⊂ M.E) : M ↾ R <m M :=
  (restrict_strictRestriction hR).strictMinor

theorem delete_contract_minor (M : Matroid α) (D C : Set α) : M ⧹ D ⧸ C ≤m M :=
  ((M ⧹ D).contract_minor C).trans (M.delete_minor D)

theorem contract_restrict_minor (M : Matroid α) (C : Set α) (hR : R ⊆ M.E \ C) :
    (M ⧸ C) ↾ R ≤m M := by
  rw [← delete_compl]; apply contract_delete_minor

theorem contractElem_strictMinor (he : e ∈ M.E) : M ⧸ e <m M :=
  ⟨contract_minor M {e}, fun hM ↦ (hM.subset he).2 rfl⟩

theorem deleteElem_strictMinor (he : e ∈ M.E) : M ⧹ e <m M :=
  ⟨delete_minor M {e}, fun hM ↦ (hM.subset he).2 rfl⟩

theorem strictMinor_iff_minor_contract_or_delete :
    N <m M ↔ ∃ e ∈ M.E, N ≤m M ⧸ e ∨ N ≤m M ⧹ e := by
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

theorem Minor.strictMinor_or_eq (h : N ≤m M) : N <m M ∨ N = M := by
  rw [strictMinor_iff_minor_ne, and_iff_right h]
  exact ne_or_eq N M

theorem Minor.dual (h : N ≤m M) : N✶ ≤m M✶ := by
  obtain ⟨C, D, -, -, -, rfl⟩ := h
  rw [delete_dual_eq_dual_contract, contract_dual_eq_dual_delete]
  apply delete_contract_minor

theorem Minor.of_dual (h : N✶ ≤m M✶) : N ≤m M := by
  simpa using h.dual

theorem dual_minor_iff : N✶ ≤m M✶ ↔ N ≤m M :=
  ⟨Minor.of_dual, Minor.dual⟩

theorem minor_dual_iff_dual_minor : N ≤m M✶ ↔ N✶ ≤m M := by
  rw [← dual_minor_iff, dual_dual]

theorem StrictMinor.dual (h : N <m M) : N✶ <m M✶ := by
  rwa [StrictMinor, dual_minor_iff, dual_minor_iff]

theorem StrictMinor.of_dual (h : N✶ <m M✶) : N <m M := by
  simpa using h.dual

theorem dual_strictMinor_iff: N✶ <m M✶ ↔ N <m M :=
  ⟨StrictMinor.of_dual, StrictMinor.dual⟩

theorem strictMinor_dual_iff_dual_strictMinor : N <m M✶ ↔ N✶ <m M := by
  rw [← dual_strictMinor_iff, dual_dual]

theorem StrictMinor.encard_ground_lt [M.Finite] (hNM : N <m M) : N.E.encard < M.E.encard :=
  M.ground_finite.encard_lt_encard hNM.ssubset

/-- The scum theorem. We can always realize a minor by contracting an independent set and deleting
  a coindependent set -/
theorem Minor.exists_contract_indep_delete_coindep (h : N ≤m M) :
    ∃ C D, M.Indep C ∧ M.Coindep D ∧ Disjoint C D ∧ N = M ⧸ C ⧹ D := by
  obtain ⟨C', D', hC', hD', hCD', rfl⟩ := h
  obtain ⟨I, hI⟩ := M.exists_basis C'
  obtain ⟨K, hK⟩ := M✶.exists_basis D'
  have hIK : Disjoint I K := disjoint_of_subset hI.subset hK.subset hCD'
  use I ∪ D' \ K, C' \ I ∪ K
  refine' ⟨_, _, _, _⟩
  · have hss : (D' \ K) \ I ⊆ (M✶ ⧸ K ⧹ I).cl ∅ := by
      rw [delete_loops_eq];
      exact diff_subset_diff_left hK.diff_subset_loops_contract
    rw [← delete_dual_eq_dual_contract, ← contract_dual_eq_dual_delete] at hss
    have hi := indep_of_subset_coloops hss
    rw [← contract_delete_comm _ hIK, delete_indep_iff, hI.indep.contract_indep_iff,
      diff_union_self, union_comm] at hi
    exact hi.1.2
  · rw [coindep_def]
    have hss : (C' \ I) \ K ⊆ (M ⧸ I ⧹ K)✶✶.cl ∅ := by
      rw [dual_dual, delete_loops_eq];
      exact diff_subset_diff_left hI.diff_subset_loops_contract
    have hi := indep_of_subset_coloops hss
    rw [delete_dual_eq_dual_contract, contract_dual_eq_dual_delete, ←
      contract_delete_comm _ hIK.symm, delete_indep_iff, hK.indep.contract_indep_iff,
      diff_union_self] at hi
    exact hi.1.2
  · rw [disjoint_union_left, disjoint_union_right, disjoint_union_right,
      and_iff_right disjoint_sdiff_right, and_iff_right hIK, and_iff_left disjoint_sdiff_left]
    exact disjoint_of_subset (diff_subset _ _) (diff_subset _ _) hCD'.symm
  have hb : (M ⧸ C')✶.Basis K D' :=
    by
    rw [contract_dual_eq_dual_delete, delete_basis_iff, and_iff_right hK]
    exact hCD'.symm
  rw [← dual_dual (M ⧸ C' ⧹ D'), delete_dual_eq_dual_contract, hb.contract_eq_contract_delete,
    hI.contract_eq_contract_delete, delete_dual_eq_dual_contract, contract_dual_eq_dual_delete,
    dual_dual, delete_delete, contract_delete_contract]
  rw [disjoint_union_right, and_iff_left disjoint_sdiff_left]
  exact disjoint_of_subset (diff_subset _ _) (diff_subset _ _) hCD'.symm

theorem Minor.exists_contract_spanning_restrict (h : N ≤m M) :
    ∃ C, M.Indep C ∧ (N ≤r M ⧸ C) ∧ (M ⧸ C).cl N.E = (M ⧸ C).E := by
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := h.exists_contract_indep_delete_coindep
  refine' ⟨C, hC, delete_restriction _ _, _⟩
  rw [← (hD.coindep_contract_of_disjoint hCD.symm).cl_compl, delete_ground]

/-- Classically choose an independent contract-set from a proof that `N` is a minor of `M`. -/
@[pp_dot] def Minor.C (h : N ≤m M) : Set α :=
  h.exists_contract_indep_delete_coindep.choose

/-- Classically choose a coindependent delete-set from a proof that `N` is a minor of `M`. -/
@[pp_dot] def Minor.D (h : N ≤m M) : Set α :=
  h.exists_contract_indep_delete_coindep.choose_spec.choose

theorem Minor.C_indep (h : N ≤m M) : M.Indep h.C := by
  obtain ⟨-,h,-⟩ := h.exists_contract_indep_delete_coindep.choose_spec; exact h

theorem Minor.D_coindep (h : N ≤m M) : M.Coindep h.D := by
  obtain ⟨-,h,-⟩ := h.exists_contract_indep_delete_coindep.choose_spec.choose_spec; exact h

theorem Minor.disjoint (h : N ≤m M) : Disjoint h.C h.D := by
  obtain ⟨-,-,h,-⟩ := h.exists_contract_indep_delete_coindep.choose_spec.choose_spec; exact h

theorem Minor.eq_con_del (h : N ≤m M) : N = M ⧸ h.C ⧹ h.D := by
  obtain ⟨-,-,-,h⟩ := h.exists_contract_indep_delete_coindep.choose_spec.choose_spec; exact h

theorem Minor.C_union_D_eq (h : N ≤m M) : h.C ∪ h.D = M.E \ N.E := by
  simp only [h.eq_con_del, delete_ground, contract_ground, diff_diff]
  rw [Set.diff_diff_cancel_left]
  exact union_subset h.C_indep.subset_ground h.D_coindep.subset_ground

theorem Minor.C_disjoint (h : N ≤m M) : Disjoint h.C N.E :=
  (subset_diff.1 h.C_union_D_eq.subset).2.mono_left (subset_union_left _ _)

theorem Minor.D_disjoint (h : N ≤m M) : Disjoint h.D N.E :=
  (subset_diff.1 h.C_union_D_eq.subset).2.mono_left (subset_union_right _ _)

theorem Minor.eq_con_restr (h : N ≤m M) : N = (M ⧸ h.C) ↾ N.E := by
  simp [h.eq_con_del, ← restrict_compl]

theorem StrictMinor.C_union_D_nonempty (h : N <m M) : (h.minor.C ∪ h.minor.D).Nonempty := by
  rw [h.minor.C_union_D_eq]
  exact nonempty_of_ssubset h.ssubset

theorem finite_setOf_minor (M : Matroid α) [M.Finite] : {N | N ≤m M}.Finite :=
  (finite_setOf_matroid M.ground_finite).subset (fun _ hNM ↦ hNM.subset)

end Minor

section Constructions

variable {E : Set α}

@[simp] theorem delete_ground_self (M : Matroid α) : M ⧹ M.E = emptyOn α := by
  simp [← ground_eq_empty_iff]

@[simp] theorem contract_ground_self (M : Matroid α) : M ⧸ M.E = emptyOn α := by
  simp [← ground_eq_empty_iff]

@[simp] theorem emptyOn_restriction (M : Matroid α) : emptyOn α ≤r M :=
  ⟨∅, empty_subset _, by simp⟩

@[simp] theorem emptyOn_minor (M : Matroid α) : emptyOn α ≤m M :=
  M.emptyOn_restriction.minor

@[simp] theorem minor_emptyOn_iff : M ≤m emptyOn α ↔ M = emptyOn α :=
  ⟨fun h ↦ ground_eq_empty_iff.1 (eq_empty_of_subset_empty h.subset),
    by rintro rfl; apply emptyOn_minor⟩

@[simp] theorem restriction_emptyOn_iff : M ≤r emptyOn α ↔ M = emptyOn α := by
  refine ⟨fun h ↦ minor_emptyOn_iff.1 h.minor, ?_⟩
  rintro rfl
  exact Restriction.refl

@[simp] theorem loopyOn_delete (E X : Set α) : (loopyOn E) ⧹ X = loopyOn (E \ X) := by
  rw [← restrict_compl, loopyOn_restrict, loopyOn_ground]

@[simp] theorem loopyOn_contract (E X : Set α) : (loopyOn E) ⧸ X = loopyOn (E \ X) := by
  simp_rw [eq_loopyOn_iff_cl, contract_cl_eq, empty_union, loopyOn_cl_eq, contract_ground,
    loopyOn_ground, true_and]

@[simp] theorem minor_loopyOn_iff : M ≤m loopyOn E ↔ M = loopyOn M.E ∧ M.E ⊆ E := by
  refine ⟨fun h ↦ ⟨by obtain ⟨C, D, _, _, _, rfl⟩ := h; simp, h.subset⟩, fun ⟨h, hss⟩ ↦ ?_⟩
  convert (loopyOn E).restrict_minor hss using 1
  rw [h, loopyOn_ground, loopyOn_restrict]

theorem contract_eq_loopyOn_of_spanning {C : Set α} (h : M.Spanning C) :
    M ⧸ C = loopyOn (M.E \ C) := by
  rw [eq_loopyOn_iff_cl, contract_ground, and_iff_left rfl, contract_cl_eq, empty_union, h.cl_eq]

@[simp] theorem freeOn_delete (E X : Set α) : (freeOn E) ⧹ X = freeOn (E \ X) := by
  rw [← loopyOn_dual_eq, ← contract_dual_eq_dual_delete, loopyOn_contract, loopyOn_dual_eq]

@[simp] theorem freeOn_contract (E X : Set α) : (freeOn E) ⧸ X = freeOn (E \ X) := by
  rw [← loopyOn_dual_eq, ← delete_dual_eq_dual_contract, loopyOn_delete, loopyOn_dual_eq]

theorem restrict_indep_eq_freeOn (hI : M.Indep I) : M ↾ I = freeOn I := by
  refine eq_of_indep_iff_indep_forall rfl (fun J _ ↦ ?_)
  simp only [restrict_ground_eq, restrict_indep_iff, freeOn_indep_iff, and_iff_right_iff_imp]
  exact hI.subset

theorem indep_iff_restrict_eq_freeOn : M.Indep I ↔ (M ↾ I = freeOn I) := by
  refine ⟨restrict_indep_eq_freeOn, fun h ↦ ?_⟩
  have h' := restrict_indep_iff (M := M) (I := I) (R := I)
  rwa [h, freeOn_indep_iff, iff_true_intro Subset.rfl, and_true, true_iff] at h'

theorem restrict_subset_loops_eq (hX : X ⊆ M.cl ∅) : M ↾ X = loopyOn X := by
  refine eq_of_indep_iff_indep_forall rfl (fun I hI ↦ ?_)
  simp only [restrict_indep_iff, loopyOn_indep_iff]
  use fun h ↦ h.1.eq_empty_of_subset_loops (h.2.trans hX)
  rintro rfl
  simp

end Constructions

end Matroid




-- theorem Flat.covby_iff_er_contract_eq (hF : M.Flat F) (hF' : M.Flat F') :
--     M.Covby F F' ↔ F ⊆ F' ∧ (M ⧸ F).er (F' \ F) = 1 :=
--   by
--   refine' (em' (F ⊆ F')).elim (fun h ↦ iff_of_false (h ∘ covby.subset) (h ∘ And.left)) fun hss ↦ _
--   obtain ⟨I, hI⟩ := M.exists_basis F
--   rw [hF.covby_iff_eq_cl_insert, and_iff_right hss]
--   refine' ⟨_, fun h ↦ _⟩
--   · rintro ⟨e, ⟨heE, heF⟩, rfl⟩
--     obtain ⟨J, hJF', rfl⟩ := hI.exists_basis_inter_eq_of_superset (subset_insert e F)
--     rw [hJF'.basis_cl.er_contract_of_subset (M.subset_cl_of_subset (subset_insert e F)) hI]
--     rw [← encard_singleton e]; apply congr_arg
--     rw [subset_antisymm_iff, diff_subset_iff, singleton_subset_iff, mem_diff, and_iff_left heF,
--       union_singleton, and_iff_right hJF'.subset]
--     by_contra heJ
--     have hJF := hF.cl_subset_of_subset ((subset_insert_iff_of_not_mem heJ).mp hJF'.subset)
--     rw [hJF'.cl] at hJF
--     exact heF (hJF (M.mem_cl_of_mem (mem_insert e F)))
--   obtain ⟨J, hJF', rfl⟩ := hI.exists_basis_inter_eq_of_superset hss
--   rw [hJF'.er_contract_of_subset hss hI, ← ENat.coe_one, encard_eq_coe_iff, ncard_eq_one] at h
--   obtain ⟨e, he⟩ := h.2; use e
--   rw [← singleton_subset_iff, ← union_singleton, ← he,
--     and_iff_right (diff_subset_diff_left hJF'.subset_ground_left), union_diff_self, ←
--     cl_union_cl_right_eq, hJF'.cl, hF'.cl, union_eq_self_of_subset_left hss, hF'.cl]

-- theorem Covby.er_contract_eq (h : M.Covby F F') : (M ⧸ F).er (F' \ F) = 1 :=
--   ((h.flat_left.covby_iff_er_contract_eq h.flat_right).mp h).2

-- theorem Hyperplane.inter_right_covby_of_inter_left_covby {H₁ H₂ : Set α} (hH₁ : M.Hyperplane H₁)
--     (hH₂ : M.Hyperplane H₂) (h : M.Covby (H₁ ∩ H₂) H₁) : M.Covby (H₁ ∩ H₂) H₂ :=
--   by
--   rw [(hH₁.flat.inter hH₂.flat).covby_iff_er_contract_eq hH₁.flat] at h
--   rw [(hH₁.flat.inter hH₂.flat).covby_iff_er_contract_eq hH₂.flat,
--     and_iff_right (inter_subset_right _ _)]
--   have h₁' := hH₁.covby.er_contract_eq
--   have h₂' := hH₂.covby.er_contract_eq
--   have h1 := M.contract_er_diff_add_contract_er_diff (inter_subset_left H₁ H₂) hH₁.subset_ground
--   have h2 := M.contract_er_diff_add_contract_er_diff (inter_subset_right H₁ H₂) hH₂.subset_ground
--   rwa [h.2, h₁', ← h2, h₂', ENat.add_eq_add_iff_right WithTop.one_ne_top, eq_comm] at h1

-- theorem Hyperplane.inter_covby_comm {H₁ H₂ : Set α} (hH₁ : M.Hyperplane H₁)
--     (hH₂ : M.Hyperplane H₂) : M.Covby (H₁ ∩ H₂) H₁ ↔ M.Covby (H₁ ∩ H₂) H₂ :=
--   ⟨hH₁.inter_right_covby_of_inter_left_covby hH₂, by rw [inter_comm]; intro h;
--     exact hH₂.inter_right_covby_of_inter_left_covby hH₁ h⟩

-- end Matroid
