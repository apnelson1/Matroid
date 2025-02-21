import Matroid.Loop
import Matroid.ForMathlib.Set

open Set

variable {α : Type*} {M M' N : Matroid α} {e f : α} {I J R B X Y Z K S : Set α}

namespace Matroid

section Delete

variable {D D₁ D₂ R : Set α}

lemma eq_loopyOn_iff_closure {E : Set α} : M = loopyOn E ↔ M.closure ∅ = E ∧ M.E = E :=
  ⟨fun h ↦ by rw [h]; simp, fun ⟨h,h'⟩ ↦ by rw [← h', ← closure_empty_eq_ground_iff, h, h']⟩

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

instance delete_rankFinite [RankFinite M] : RankFinite (M ＼ D) :=
  restrict_rankFinite _

lemma restrict_compl (M : Matroid α) (D : Set α) : M ↾ (M.E \ D) = M ＼ D := rfl

@[simp] lemma delete_compl (hR : R ⊆ M.E := by aesop_mat) : M ＼ (M.E \ R) = M ↾ R := by
  rw [← restrict_compl, diff_diff_cancel_left hR]

@[simp] lemma delete_isRestriction (M : Matroid α) (D : Set α) : M ＼ D ≤r M :=
  restrict_isRestriction _ _ diff_subset

lemma IsRestriction.exists_eq_delete (hNM : N ≤r M) : ∃ D ⊆ M.E, N = M ＼ D :=
  ⟨M.E \ N.E, diff_subset, by obtain ⟨R, hR, rfl⟩ := hNM; rw [delete_compl, restrict_ground_eq]⟩

lemma isRestriction_iff_exists_eq_delete : N ≤r M ↔ ∃ D ⊆ M.E, N = M ＼ D :=
  ⟨IsRestriction.exists_eq_delete, by rintro ⟨D, -, rfl⟩; apply delete_isRestriction⟩

@[simp] lemma delete_ground (M : Matroid α) (D : Set α) : (M ＼ D).E = M.E \ D := rfl

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma delete_subset_ground (M : Matroid α) (D : Set α) : (M ＼ D).E ⊆ M.E :=
  diff_subset

@[simp] lemma deleteElem (M : Matroid α) (e : α) : M ＼ e = M ＼ ({e} : Set α) := rfl

lemma deleteElem_eq_self (he : e ∉ M.E) : M ＼ e = M := by
  rwa [deleteElem, delete_eq_restrict, restrict_eq_self_iff, sdiff_eq_left,
    disjoint_singleton_right]

instance deleteElem_rankFinite [RankFinite M] {e : α} : RankFinite (M ＼ e) := by
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

lemma IsRestriction.restrict_delete_of_disjoint (h : N ≤r M) (hX : Disjoint X N.E) :
    N ≤r (M ＼ X) := by
  obtain ⟨D, hD, rfl⟩ := isRestriction_iff_exists_eq_delete.1 h
  refine isRestriction_iff_exists_eq_delete.2 ⟨D \ X, diff_subset_diff_left hD, ?_⟩
  rwa [delete_delete, union_diff_self, union_comm, ← delete_delete, eq_comm,
    delete_eq_self_iff]

lemma IsRestriction.restriction_deleteElem (h : N ≤r M) (he : e ∉ N.E) : N ≤r M ＼ e :=
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

@[simp] lemma delete_isBase_iff : (M ＼ D).IsBase B ↔ M.IsBasis B (M.E \ D) := by
  rw [← restrict_compl, isBase_restrict_iff]

@[simp] lemma delete_isBasis_iff : (M ＼ D).IsBasis I X ↔ M.IsBasis I X ∧ Disjoint X D := by
  rw [← restrict_compl, isBasis_restrict_iff, subset_diff, ← and_assoc,
    and_iff_left_of_imp IsBasis.subset_ground]

@[simp] lemma delete_isBasis'_iff : (M ＼ D).IsBasis' I X ↔ M.IsBasis' I (X \ D) := by
  rw [isBasis'_iff_isBasis_inter_ground, delete_isBasis_iff, delete_ground, diff_eq, inter_comm M.E,
    ← inter_assoc, ← diff_eq, ← isBasis'_iff_isBasis_inter_ground, and_iff_left_iff_imp,
    inter_comm, ← inter_diff_assoc]
  exact fun _ ↦ disjoint_sdiff_left

lemma IsBasis.of_delete (h : (M ＼ D).IsBasis I X) : M.IsBasis I X :=
  (delete_isBasis_iff.mp h).1

lemma IsBasis.to_delete (h : M.IsBasis I X) (hX : Disjoint X D) : (M ＼ D).IsBasis I X := by
  rw [delete_isBasis_iff]; exact ⟨h, hX⟩

@[simp] lemma delete_isLoop_iff : (M ＼ D).IsLoop e ↔ M.IsLoop e ∧ e ∉ D := by
  rw [← singleton_dep, delete_dep_iff, disjoint_singleton_left, singleton_dep]

@[simp] lemma delete_isNonloop_iff : (M ＼ D).IsNonloop e ↔ M.IsNonloop e ∧ e ∉ D := by
  rw [← indep_singleton, delete_indep_iff, disjoint_singleton_left, indep_singleton]

lemma IsNonloop.of_delete (h : (M ＼ D).IsNonloop e) : M.IsNonloop e :=
  (delete_isNonloop_iff.1 h).1

lemma isNonloop_iff_delete_of_not_mem (he : e ∉ D) : M.IsNonloop e ↔ (M ＼ D).IsNonloop e :=
  ⟨fun h ↦ delete_isNonloop_iff.2 ⟨h, he⟩, fun h ↦ h.of_delete⟩

@[simp] lemma delete_isCircuit_iff {C : Set α} :
    (M ＼ D).IsCircuit C ↔ M.IsCircuit C ∧ Disjoint C D := by
  simp_rw [isCircuit_iff, delete_dep_iff, and_imp]
  rw [and_comm, ← and_assoc, and_congr_left_iff, and_comm, and_congr_right_iff]
  exact fun hdj _↦ ⟨fun h I hId hIC ↦ h hId (disjoint_of_subset_left hIC hdj) hIC,
    fun h I hI _ hIC ↦ h hI hIC⟩

lemma IsCircuit.of_delete {C : Set α} (h : (M ＼ D).IsCircuit C) : M.IsCircuit C :=
  (delete_isCircuit_iff.1 h).1

lemma circuit_iff_delete_of_disjoint {C : Set α} (hCD : Disjoint C D) :
    M.IsCircuit C ↔ (M ＼ D).IsCircuit C :=
  ⟨fun h ↦ delete_isCircuit_iff.2 ⟨h, hCD⟩, fun h ↦ h.of_delete⟩

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
  simp [Set.ext_iff, mem_setOf, IsNonloop, IsLoop, mem_diff, and_comm]

lemma removeLoops_del_eq_removeLoops (h : X ⊆ M.closure ∅) :
    (M ＼ X).removeLoops = M.removeLoops := by
  rw [removeLoops_eq_delete, delete_delete, removeLoops_eq_delete, delete_closure_eq, empty_diff,
    union_diff_self, union_eq_self_of_subset_left h]

lemma Coindep.delete_isBase_iff (hD : M.Coindep D) :
    (M ＼ D).IsBase B ↔ M.IsBase B ∧ Disjoint B D := by
  rw [Matroid.delete_isBase_iff]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hss := h.subset
    rw [subset_diff] at hss
    have hcl := h.isBasis_closure_right
    rw [hD.closure_compl, isBasis_ground_iff] at hcl
    exact ⟨hcl, hss.2⟩
  exact h.1.isBasis_ground.isBasis_subset (by simp [subset_diff, h.1.subset_ground, h.2])
    diff_subset

lemma Coindep.delete_rankPos [M.RankPos] (hD : M.Coindep D) : (M ＼ D).RankPos := by
  simp [rankPos_iff, hD.delete_isBase_iff, M.empty_not_isBase]

lemma Coindep.delete_spanning_iff (hD : M.Coindep D) :
    (M ＼ D).Spanning S ↔ M.Spanning S ∧ Disjoint S D := by
  simp only [spanning_iff_exists_isBase_subset', hD.delete_isBase_iff, and_assoc, delete_ground,
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

@[simp] lemma contractElem (M : Matroid α) (e : α) : M ／ e = M ／ ({e} : Set α) :=
  rfl

lemma contractElem_eq_self (he : e ∉ M.E) : M ／ e = M := by
  rw [contractElem, ← dual_delete_dual_eq_contract, ← deleteElem, deleteElem_eq_self (by simpa),
    dual_dual]

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

@[simp] lemma contract_isCocircuit_iff :
    (M ／ C).IsCocircuit K ↔ M.IsCocircuit K ∧ Disjoint K C := by
  rw [isCocircuit_def, contract_dual_eq_dual_delete, delete_isCircuit_iff]

lemma Indep.contract_isBase_iff (hI : M.Indep I) :
    (M ／ I).IsBase B ↔ M.IsBase (B ∪ I) ∧ Disjoint B I := by
  have hIE := hI.subset_ground
  rw [← dual_dual M, ← coindep_def, coindep_iff_exists] at hI
  obtain ⟨B₀, hB₀, hfk⟩ := hI
  rw [← dual_dual M, ← dual_delete_dual_eq_contract, dual_isBase_iff', dual_isBase_iff',
    delete_isBase_iff, dual_dual, delete_ground, diff_diff, union_comm, union_subset_iff,
    subset_diff, ← and_assoc, and_congr_left_iff, dual_ground, and_iff_left hIE, and_congr_left_iff]
  refine fun _ _ ↦
    ⟨fun h ↦ h.isBase_of_isBase_subset hB₀ (subset_diff.mpr ⟨hB₀.subset_ground, ?_⟩), fun hB ↦
      hB.isBasis_of_subset diff_subset (diff_subset_diff_right subset_union_right)⟩
  exact disjoint_of_subset_left hfk disjoint_sdiff_left

lemma Indep.contract_indep_iff (hI : M.Indep I) :
    (M ／ I).Indep J ↔ Disjoint J I ∧ M.Indep (J ∪ I) := by
  simp_rw [indep_iff, hI.contract_isBase_iff, union_subset_iff]
  exact ⟨fun ⟨B, ⟨hBI, hdj⟩, hJB⟩ ↦
    ⟨disjoint_of_subset_left hJB hdj, _, hBI, hJB.trans subset_union_left,
      subset_union_right⟩,
    fun ⟨hdj, B, hB, hJB, hIB⟩ ↦ ⟨B \ I,⟨by simpa [union_eq_self_of_subset_right hIB],
      disjoint_sdiff_left⟩, subset_diff.2 ⟨hJB, hdj⟩ ⟩⟩

lemma IsNonloop.contract_indep_iff (he : M.IsNonloop e) :
    (M ／ e).Indep I ↔ e ∉ I ∧ M.Indep (insert e I) := by
  simp [contractElem, he.indep.contract_indep_iff]

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

lemma Indep.union_isBasis_union_of_contract_isBasis (hI : M.Indep I) (hB : (M ／ I).IsBasis J X) :
    M.IsBasis (J ∪ I) (X ∪ I) := by
  have hi := hB.indep
  rw [hI.contract_indep_iff] at hi
  refine hi.2.isBasis_of_maximal_subset (union_subset_union_left _ hB.subset) ?_ ?_
  · intro K hK hJIK hKXI
    rw [union_subset_iff] at hJIK
    have hK' : (M ／ I).Indep (K \ I) := hK.diff_indep_contract_of_subset hJIK.2
    have hm := hB.eq_of_subset_indep hK'
    rw [subset_diff, and_iff_left hi.1, diff_subset_iff, union_comm, imp_iff_right hKXI,
      imp_iff_right hJIK.1] at hm
    simp [hm]
  exact union_subset (hB.subset_ground.trans (contract_ground_subset_ground _ _)) hI.subset_ground

lemma IsBasis'.contract_isBasis'_diff_diff_of_subset (hIX : M.IsBasis' I X) (hJI : J ⊆ I) :
    (M ／ J).IsBasis' (I \ J) (X \ J) := by
  suffices ∀ ⦃K⦄, Disjoint K J → M.Indep (K ∪ J) → K ⊆ X → I ⊆ K ∪ J → K ⊆ I by
    simpa +contextual [IsBasis', (hIX.indep.subset hJI).contract_indep_iff,
      subset_diff, maximal_subset_iff, disjoint_sdiff_left,
      union_eq_self_of_subset_right hJI, hIX.indep, diff_subset.trans hIX.subset,
      diff_subset_iff, subset_antisymm_iff, union_comm J]

  exact fun K hJK hKJi hKX hIJK ↦ by
    simp [hIX.eq_of_subset_indep hKJi hIJK (union_subset hKX (hJI.trans hIX.subset))]

lemma IsBasis'.contract_isBasis'_diff_of_subset (hIX : M.IsBasis' I X) (hJI : J ⊆ I) :
    (M ／ J).IsBasis' (I \ J) X := by
  rw [isBasis'_iff_isBasis_inter_ground]
  simpa [inter_diff_assoc] using
    (hIX.contract_isBasis'_diff_diff_of_subset hJI).isBasis_inter_ground

lemma IsBasis.contract_isBasis_diff_diff_of_subset (hIX : M.IsBasis I X) (hJI : J ⊆ I) :
    (M ／ J).IsBasis (I \ J) (X \ J) := by
  have h := (hIX.isBasis'.contract_isBasis'_diff_of_subset hJI).isBasis_inter_ground
  rwa [contract_ground, ← inter_diff_assoc, inter_eq_self_of_subset_left hIX.subset_ground] at h

lemma IsBasis.contract_diff_isBasis_diff (hIX : M.IsBasis I X) (hJY : M.IsBasis J Y) (hIJ : I ⊆ J) :
    (M ／ I).IsBasis (J \ I) (Y \ X) := by
  refine (hJY.contract_isBasis_diff_diff_of_subset hIJ).isBasis_subset ?_ ?_
  · rw [subset_diff, and_iff_right (diff_subset.trans hJY.subset),
      hIX.eq_of_subset_indep (hJY.indep.inter_right X) (subset_inter hIJ hIX.subset)
      inter_subset_right, diff_self_inter]
    exact disjoint_sdiff_left
  refine diff_subset_diff_right hIX.subset

lemma IsBasis.contract_isBasis_union_union (h : M.IsBasis (J ∪ I) (X ∪ I))
    (hJI : Disjoint J I) (hXI : Disjoint X I) : (M ／ I).IsBasis J X := by
  have  h' : (M ／ I).IsBasis' J X := by
    simpa [hXI.sdiff_eq_left, hJI.sdiff_eq_left] using
    h.isBasis'.contract_isBasis'_diff_diff_of_subset subset_union_right

  rwa [isBasis'_iff_isBasis _ ] at h'
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

lemma IsBasis.contract_eq_contract_delete (hI : M.IsBasis I X) : M ／ X = M ／ I ＼ (X \ I) := by
  nth_rw 1 [← diff_union_of_subset hI.subset]
  rw [union_comm, ← contract_contract]
  refine contract_eq_delete_of_subset_loops fun e he ↦ ?_
  rw [← isLoop_iff_mem_closure_empty, ← singleton_dep, hI.indep.contract_dep_iff,
    disjoint_singleton_left, and_iff_right he.2, singleton_union,
    ← hI.indep.mem_closure_iff_of_not_mem he.2]
  exact hI.subset_closure he.1

lemma IsBasis'.contract_eq_contract_delete (hI : M.IsBasis' I X) : M ／ X = M ／ I ＼ (X \ I) := by
  rw [← contract_inter_ground_eq, hI.isBasis_inter_ground.contract_eq_contract_delete, eq_comm,
    ← delete_inter_ground_eq, contract_ground, diff_eq, diff_eq, ← inter_inter_distrib_right,
    ← diff_eq]

lemma IsBasis'.contract_indep_iff (hI : M.IsBasis' I X) :
    (M ／ X).Indep J ↔ M.Indep (J ∪ I) ∧ Disjoint X J := by
  rw [hI.contract_eq_contract_delete, delete_indep_iff, hI.indep.contract_indep_iff,
    and_comm, ← and_assoc, ← disjoint_union_right, diff_union_self,
    union_eq_self_of_subset_right hI.subset, and_comm, disjoint_comm]

lemma IsBasis.contract_indep_iff (hI : M.IsBasis I X) :
    (M ／ X).Indep J ↔ M.Indep (J ∪ I) ∧ Disjoint X J :=
  hI.isBasis'.contract_indep_iff

lemma IsBasis.contract_indep_diff_iff (hI : M.IsBasis I X) :
    (M ／ X).Indep (J \ X) ↔ M.Indep ((J \ X) ∪ I) := by
  rw [hI.contract_indep_iff, and_iff_left disjoint_sdiff_right]

lemma IsBasis'.contract_indep_diff_iff (hI : M.IsBasis' I X) :
    (M ／ X).Indep (J \ X) ↔ M.Indep ((J \ X) ∪ I) := by
  rw [hI.contract_indep_iff, and_iff_left disjoint_sdiff_right]

lemma contract_closure_eq_contract_delete (M : Matroid α) (C : Set α) :
    M ／ M.closure C = M ／ C ＼ (M.closure C \ C) := by
  obtain ⟨I, hI⟩ := M.exists_isBasis_inter_ground_isBasis_closure C
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
    ∃ I D : Set α, M.IsBasis I (C ∩ M.E) ∧ D ⊆ (M ／ I).E ∧ D ⊆ C ∧ M ／ C = M ／ I ＼ D := by
  obtain ⟨I, hI⟩ := M.exists_isBasis (C ∩ M.E)
  use I, C \ I ∩ M.E, hI
  rw [contract_ground, and_iff_right (inter_subset_left.trans diff_subset), diff_eq,
    diff_eq, inter_right_comm, inter_assoc, and_iff_right inter_subset_right,
    ← contract_inter_ground_eq, hI.contract_eq_contract_delete, diff_eq, inter_assoc]

lemma Indep.of_contract (hI : (M ／ C).Indep I) : M.Indep I := by
  obtain ⟨J, R, hJ, -, -, hM⟩ := M.exists_eq_contract_indep_delete C
  rw [hM, delete_indep_iff, hJ.indep.contract_indep_iff] at hI
  exact hI.1.2.subset subset_union_left

instance contract_rankFinite [RankFinite M] : RankFinite (M ／ C) := by
  obtain ⟨B, hB⟩ := (M ／ C).exists_isBase
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

instance contractElem_rankFinite [RankFinite M] {e : α} : RankFinite (M ／ e) := by
  rw [contractElem]; infer_instance

instance contractElem_finitary [Finitary M] {e : α} : Finitary (M ／ e) := by
  rw [contractElem]; infer_instance

@[simp] lemma contract_isLoop_iff_mem_closure : (M ／ C).IsLoop e ↔ e ∈ M.closure C \ C := by
  obtain ⟨I, D, hI, -, -, hM⟩ := M.exists_eq_contract_indep_delete C
  rw [hM, delete_isLoop_iff, ← singleton_dep, hI.indep.contract_dep_iff, disjoint_singleton_left,
    singleton_union, hI.indep.insert_dep_iff, mem_diff, ← M.closure_inter_ground C,
    hI.closure_eq_closure, and_comm (a := e ∉ I), and_self_right, ← mem_diff, ← mem_diff, diff_diff]
  apply_fun Matroid.E at hM
  rw [delete_ground, contract_ground, contract_ground, diff_diff, diff_eq_diff_iff_inter_eq_inter,
    inter_comm, inter_comm M.E] at hM
  exact
    ⟨fun h ↦ ⟨h.1, fun heC ↦ h.2 (hM.subset ⟨heC, M.closure_subset_ground _ h.1⟩).1⟩, fun h ↦
      ⟨h.1, fun h' ↦ h.2 (hM.symm.subset ⟨h', M.closure_subset_ground _ h.1⟩).1⟩⟩

lemma contract_loops_eq : (M ／ C).closure ∅ = M.closure C \ C := by
  simp [Set.ext_iff, ← isLoop_iff_mem_closure_empty, contract_isLoop_iff_mem_closure]

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
  rw [← contract_isLoop_iff_mem_closure, ← contract_isLoop_iff_mem_closure, contract_contract,
    union_comm]

-- TODO : `Basis'` version.
lemma IsBasis.contract_isBasis (hIC : M.IsBasis I C) (hJY : M.IsBasis J Y)
    (h_ind : M.Indep (J \ C ∪ I)) : (M ／ C).IsBasis (J \ C) (Y \ C) := by
  refine Indep.isBasis_of_subset_of_subset_closure ?_ (diff_subset_diff_left hJY.subset) ?_
  · rwa [hIC.contract_indep_diff_iff]
  simp only [contract_closure_eq, diff_union_self, closure_union_congr_left hJY.closure_eq_closure]
  exact diff_subset_diff_left (subset_closure_of_subset _ subset_union_left)

lemma IsBasis.contract_isBasis_of_disjoint (hIC : M.IsBasis I C) (hJY : M.IsBasis J Y)
    (hdj : Disjoint C Y) (h_ind : M.Indep (I ∪ J)) : (M ／ C).IsBasis J Y := by
  refine Indep.isBasis_of_subset_of_subset_closure ?_ hJY.subset ?_
  · rwa [hIC.contract_indep_iff, and_iff_left (hdj.mono_right hJY.subset), union_comm]
  rw [contract_closure_eq, subset_diff, and_iff_left hdj.symm, closure_union_congr_left
    hJY.closure_eq_closure]
  exact subset_closure_of_subset _ subset_union_left

-- TODO : `Basis'` version.
lemma Indep.contract_isBasis (hI : M.Indep I) (hJY : M.IsBasis J Y) (h_ind : M.Indep (I ∪ J)) :
    (M ／ I).IsBasis (J \ I) (Y \ I) := by
  refine Indep.isBasis_of_subset_of_subset_closure ?_ (diff_subset_diff_left hJY.subset) ?_
  · rwa [hI.contract_indep_iff, and_iff_right disjoint_sdiff_left, diff_union_self, union_comm]
  simp only [contract_closure_eq, diff_union_self, closure_union_congr_left hJY.closure_eq_closure]
  exact diff_subset_diff_left <| subset_closure_of_subset _ subset_union_left

lemma Indep.contract_isBasis_of_disjoint (hI : M.Indep I) (hJY : M.IsBasis J Y) (hdj : Disjoint I Y)
    (h_ind : M.Indep (I ∪ J)) : (M ／ I).IsBasis J Y := by
  have hb := hI.contract_isBasis hJY h_ind
  rwa [hdj.sdiff_eq_right, (hdj.mono_right hJY.subset).sdiff_eq_right] at hb

lemma IsCircuit.contract_dep (hK : M.IsCircuit K) (hCK : Disjoint C K) : (M ／ C).Dep K := by
  obtain ⟨I, hI⟩ := M.exists_isBasis (C ∩ M.E)
  rw [← contract_inter_ground_eq, Dep, hI.contract_indep_iff,
    and_iff_left (hCK.mono_left inter_subset_left), contract_ground, subset_diff,
    and_iff_left (hCK.symm.mono_right inter_subset_left), and_iff_left hK.subset_ground]
  exact fun hi ↦ hK.dep.not_indep (hi.subset subset_union_left)

lemma IsCircuit.contract_isCircuit (hK : M.IsCircuit K) (hC : C ⊂ K) :
    (M ／ C).IsCircuit (K \ C) := by
  have hCi := hK.ssubset_indep hC
  rw [isCircuit_iff_forall_ssubset, hCi.contract_dep_iff, and_iff_right (disjoint_sdiff_left),
    diff_union_self, union_eq_self_of_subset_right hC.subset, and_iff_right hK.dep]
  intro I hI
  rw [ssubset_iff_subset_not_subset, subset_diff, diff_subset_iff, union_comm] at hI
  rw [hCi.contract_indep_iff, and_iff_right hI.1.2]
  refine hK.ssubset_indep <| (union_subset hI.1.1 hC.subset).ssubset_of_ne ?_
  rintro rfl
  exact hI.2 Subset.rfl

lemma IsCircuit.contractElem_isCircuit (hC : M.IsCircuit C) (hnt : C.Nontrivial) (heC : e ∈ C) :
    (M ／ e).IsCircuit (C \ {e}) :=
  hC.contract_isCircuit (ssubset_of_ne_of_subset hnt.ne_singleton.symm (by simpa))

lemma IsCircuit.contract_dep_of_not_subset (hK : M.IsCircuit K) {C : Set α} (hKC : ¬ K ⊆ C) :
    (M ／ C).Dep (K \ C) := by
  have h' := hK.contract_isCircuit (C := C ∩ K) (inter_subset_right.ssubset_of_ne (by simpa))
  simp only [diff_inter_self_eq_diff] at h'
  have hwin := h'.contract_dep (C := C \ K) disjoint_sdiff_sdiff
  rwa [contract_contract, inter_union_diff] at hwin

lemma IsCircuit.contract_diff_isCircuit (hC : M.IsCircuit C) (hK : K.Nonempty) (hKC : K ⊆ C) :
    (M ／ (C \ K)).IsCircuit K := by
  simpa [inter_eq_self_of_subset_right hKC] using hC.contract_isCircuit (diff_ssubset hKC hK)

lemma IsCircuit.subset_isCircuit_of_contract {C K : Set α} (hC : (M ／ K).IsCircuit C) :
    ∃ C', M.IsCircuit C' ∧ C ⊆ C' ∧ C' ⊆ C ∪ K := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' K
  rw [hI.contract_eq_contract_delete, delete_isCircuit_iff] at hC

  have hCss := hC.1.subset_ground
  rw [contract_ground, subset_diff] at hCss
  obtain ⟨hCE, hCI⟩ := hCss
  have hIE := hI.indep.subset_ground

  have hCId : M.Dep (C ∪ I) := by
    rw [← not_indep_iff]; intro hd
    have hCi := hd.diff_indep_contract_of_subset subset_union_right
    rw [union_diff_right, sdiff_eq_left.2 hCI] at hCi
    exact hC.1.dep.not_indep hCi

  obtain ⟨C', hC'CI, hC'⟩ := hCId.exists_isCircuit_subset
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

lemma IsBasis.diff_subset_loops_contract (hIX : M.IsBasis I X) : X \ I ⊆ (M ／ I).closure ∅ := by
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

lemma IsNonloop.of_contract (h : (M ／ C).IsNonloop e) : M.IsNonloop e := by
  rw [← indep_singleton] at h ⊢
  exact h.of_contract

@[simp] lemma contract_isNonloop_iff : (M ／ C).IsNonloop e ↔ e ∈ M.E \ M.closure C := by
  rw [isNonloop_iff_mem_compl_loops, contract_ground, contract_loops_eq]
  refine ⟨fun ⟨he,heC⟩ ↦ ⟨he.1, fun h ↦ heC ⟨h, he.2⟩⟩,
    fun h ↦ ⟨⟨h.1, fun heC ↦ h.2 ?_⟩, fun h' ↦ h.2 h'.1⟩⟩
  rw [← closure_inter_ground]
  exact (M.subset_closure (C ∩ M.E)) ⟨heC, h.1⟩

lemma IsCocircuit.of_contract (hK : (M ／ C).IsCocircuit K) : M.IsCocircuit K := by
  rw [isCocircuit_def, contract_dual_eq_dual_delete] at hK
  exact hK.of_delete

lemma IsCocircuit.delete_isCocircuit {D : Set α} (hK : M.IsCocircuit K) (hD : D ⊂ K) :
    (M ＼ D).IsCocircuit (K \ D) := by
  rw [isCocircuit_def, delete_dual_eq_dual_contract]
  exact hK.isCircuit.contract_isCircuit hD

lemma IsCocircuit.delete_diff_isCocircuit {X : Set α} (hK : M.IsCocircuit K) (hXK : X ⊆ K)
    (hX : X.Nonempty) : (M ＼ (K \ X)).IsCocircuit X := by
  rw [isCocircuit_def, delete_dual_eq_dual_contract]
  exact hK.isCircuit.contract_diff_isCircuit hX hXK

end Contract

section IsMinor

variable {M₀ M₁ M₂ : Matroid α}

lemma contract_delete_diff (M : Matroid α) (C D : Set α) : M ／ C ＼ D = M ／ C ＼ (D \ C) := by
  rw [delete_eq_delete_iff, contract_ground, diff_eq, diff_eq, ← inter_inter_distrib_right,
    inter_assoc]

lemma contract_restrict_eq_restrict_contract (M : Matroid α) (C R : Set α) (h : Disjoint C R) :
    (M ／ C) ↾ R = (M ↾ (R ∪ C)) ／ C := by
  refine ext_indep (by simp [h.sdiff_eq_right]) (fun I _ ↦ ?_)
  obtain ⟨J, hJ⟩ := (M ↾ (R ∪ C)).exists_isBasis' C
  have hJ' : M.IsBasis' J C := by
    have := (isBasis'_restrict_iff.1 hJ).1
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
  obtain ⟨J, hJ⟩ := (M ＼ D).exists_isBasis' C;  have hJ' := hJ
  rw [← restrict_compl, isBasis'_restrict_iff, subset_diff, diff_eq, inter_comm M.E, ← inter_assoc,
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
def IsMinor (N M : Matroid α) : Prop :=
  ∃ C D, C ⊆ M.E ∧ D ⊆ M.E ∧ Disjoint C D ∧ N = M ／ C ＼ D

def IsStrictMinor (N M : Matroid α) : Prop :=
  IsMinor N M ∧ ¬IsMinor M N

infixl:50 " ≤m " => Matroid.IsMinor
infixl:50 " <m " => Matroid.IsStrictMinor

lemma contract_delete_isMinor (M : Matroid α) (C D : Set α) : M ／ C ＼ D ≤m M := by
  rw [contract_delete_diff, ← contract_inter_ground_eq, ← delete_inter_ground_eq,
    contract_ground, diff_inter_self_eq_diff, diff_inter_diff_right, inter_diff_right_comm]
  refine ⟨_,_, inter_subset_right, inter_subset_right, ?_, rfl⟩
  exact disjoint_of_subset inter_subset_left inter_subset_left disjoint_sdiff_right

lemma isMinor_def : N ≤m M ↔ ∃ C D, C ⊆ M.E ∧ D ⊆ M.E ∧ Disjoint C D ∧ N = M ／ C ＼ D := Iff.rfl

lemma isMinor_iff_exists_contract_delete : N ≤m M ↔ ∃ C D : Set α, N = M ／ C ＼ D :=
  ⟨fun ⟨C, D, h⟩ ↦ ⟨_,_,h.2.2.2⟩, fun ⟨C, D, h⟩ ↦ by rw [h]; apply contract_delete_isMinor⟩

lemma Indep.of_isMinor (hI : N.Indep I) (hNM : N ≤m M) : M.Indep I := by
  obtain ⟨C,D, rfl⟩ := isMinor_iff_exists_contract_delete.1 hNM
  exact hI.of_delete.of_contract

lemma IsNonloop.of_isMinor (h : N.IsNonloop e) (hNM : N ≤m M) : M.IsNonloop e := by
  obtain ⟨C, D, rfl⟩ := isMinor_iff_exists_contract_delete.1 hNM
  exact h.of_delete.of_contract

lemma IsLoop.of_isMinor (he : M.IsLoop e) (heN : e ∈ N.E) (hNM : N ≤m M) : N.IsLoop e := by
  rw [← not_isNonloop_iff]
  exact fun hnl ↦ he.not_isNonloop <| hnl.of_isMinor hNM

lemma IsMinor.eq_of_ground_subset (h : N ≤m M) (hE : M.E ⊆ N.E) : M = N := by
  obtain ⟨C, D, -, -, -, rfl⟩ := h
  rw [delete_ground, contract_ground, subset_diff, subset_diff] at hE
  rw [← contract_inter_ground_eq, hE.1.2.symm.inter_eq, contract_empty, ← delete_inter_ground_eq,
    hE.2.symm.inter_eq, delete_empty]

lemma IsMinor.subset (h : N ≤m M) : N.E ⊆ M.E := by
  obtain ⟨C, D, -, -, -, rfl⟩ := h; exact diff_subset.trans diff_subset

lemma IsMinor.refl {M : Matroid α} : M ≤m M :=
  isMinor_iff_exists_contract_delete.2 ⟨∅, ∅, by simp⟩

lemma IsMinor.trans {M₁ M₂ M₃ : Matroid α} (h : M₁ ≤m M₂) (h' : M₂ ≤m M₃) : M₁ ≤m M₃ := by
  obtain ⟨C₁, D₁, -, -, -, rfl⟩ := h
  obtain ⟨C₂, D₂, -, -, -, rfl⟩ := h'
  rw [contract_delete_contract_delete']
  apply contract_delete_isMinor

lemma IsMinor.antisymm (h : N ≤m M) (h' : M ≤m N) : N = M :=
  h'.eq_of_ground_subset h.subset

/-- The minor order is a `PartialOrder` on `Matroid α`. We prefer the spelling `M ≤m M'`
  to `M ≤ M'` for the dot notation. -/
instance (α : Type*) : PartialOrder (Matroid α) where
  le M M' := M ≤m M'
  lt M M' := M <m M'
  le_refl M := IsMinor.refl
  le_trans _ _ _ h h' := IsMinor.trans h h'
  le_antisymm _ _ h h' := IsMinor.antisymm h h'

lemma IsMinor.finite (h : N ≤m M) [M.Finite] : N.Finite :=
  ⟨M.ground_finite.subset h.subset⟩

lemma IsMinor.rankFinite (h : N ≤m M) [RankFinite M] : RankFinite N := by
  obtain ⟨C, D, rfl⟩ := isMinor_iff_exists_contract_delete.1 h
  infer_instance

lemma IsMinor.finitary (h : N ≤m M) [Finitary M] : Finitary N := by
  obtain ⟨C, D, rfl⟩ := isMinor_iff_exists_contract_delete.1 h
  infer_instance

lemma IsMinor.le (h : N ≤m M) : N ≤ M := h

lemma IsStrictMinor.lt (h : N <m M) : N < M := h

@[simp] protected lemma le_iff (M M' : Matroid α) : M ≤ M' ↔ M ≤m M' := Iff.rfl

@[simp] protected lemma lt_iff (M M' : Matroid α) : M < M' ↔ M <m M' := Iff.rfl

lemma IsStrictMinor.isMinor (h : N <m M) : N ≤m M :=
  h.lt.le

lemma IsStrictMinor.not_isMinor (h : N <m M) : ¬ (M ≤m N) :=
  h.lt.not_le

lemma isStrictMinor_iff_isMinor_ne : N <m M ↔ N ≤m M ∧ N ≠ M :=
  lt_iff_le_and_ne (α := Matroid α)

lemma IsStrictMinor.ne (h : N <m M) : N ≠ M :=
  LT.lt.ne h

lemma isStrictMinor_irrefl (M : Matroid α) : ¬ (M <m M) :=
  lt_irrefl M

lemma IsStrictMinor.ssubset (h : N <m M) : N.E ⊂ M.E :=
  h.isMinor.subset.ssubset_of_ne (fun hE ↦ h.ne (h.isMinor.eq_of_ground_subset hE.symm.subset).symm)

lemma isStrictMinor_iff_isMinor_ssubset : N <m M ↔ N ≤m M ∧ N.E ⊂ M.E :=
  ⟨fun h ↦ ⟨h.isMinor, h.ssubset⟩, fun ⟨h, hss⟩ ↦ ⟨h, fun h' ↦ hss.ne <| by rw [h'.antisymm h]⟩⟩

lemma IsStrictMinor.trans_isMinor (h : N <m M) (h' : M ≤m M') : N <m M' :=
  h.lt.trans_le h'

lemma IsMinor.trans_isStrictMinor (h : N ≤m M) (h' : M <m M') : N <m M' :=
  h.le.trans_lt h'

lemma IsStrictMinor.trans (h : N <m M) (h' : M <m M') : N <m M' :=
  h.lt.trans h'

lemma isStrictMinor_iff_exists_eq_contract_delete :
    N <m M ↔ ∃ C D, C ⊆ M.E ∧ D ⊆ M.E ∧ Disjoint C D ∧ (C ∪ D).Nonempty ∧ N = M ／ C ＼ D := by
  rw [isStrictMinor_iff_isMinor_ssubset, isMinor_def]
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

lemma contract_isMinor (M : Matroid α) (C : Set α) : M ／ C ≤m M := by
  rw [← (M ／ C).delete_empty]; apply contract_delete_isMinor

lemma contract_isMinor_of_subset (M : Matroid α) {C C' : Set α} (hCC' : C ⊆ C') :
    M ／ C' ≤m M ／ C := by
  rw [← diff_union_of_subset hCC', union_comm, ← contract_contract]
  apply contract_isMinor

lemma contract_isMinor_of_mem (M : Matroid α) {C : Set α} (he : e ∈ C) :
    M ／ C ≤m M ／ e :=
  M.contract_isMinor_of_subset (singleton_subset_iff.2 he)

lemma delete_isMinor (M : Matroid α) (D : Set α) : M ＼ D ≤m M := by
  nth_rw 1 [← M.contract_empty]; apply contract_delete_isMinor

lemma restrict_isMinor (M : Matroid α) (hR : R ⊆ M.E := by aesop_mat) : (M ↾ R) ≤m M := by
  rw [← delete_compl]; apply delete_isMinor

lemma IsRestriction.isMinor (h : N ≤r M) : N ≤m M := by
  rw [← h.eq_restrict, ← delete_compl h.subset]; apply delete_isMinor

lemma IsStrictRestriction.isStrictMinor (h : N <r M) : N <m M :=
  ⟨h.isRestriction.isMinor, fun h' ↦ h.ssubset.not_subset h'.subset⟩

lemma restrict_isStrictMinor (hR : R ⊂ M.E) : M ↾ R <m M :=
  (restrict_isStrictRestriction hR).isStrictMinor

lemma delete_contract_isMinor (M : Matroid α) (D C : Set α) : M ＼ D ／ C ≤m M :=
  ((M ＼ D).contract_isMinor C).trans (M.delete_isMinor D)

lemma contract_restrict_isMinor (M : Matroid α) (C : Set α) (hR : R ⊆ M.E \ C) :
    (M ／ C) ↾ R ≤m M := by
  rw [← delete_compl]; apply contract_delete_isMinor

lemma contractElem_isStrictMinor (he : e ∈ M.E) : M ／ e <m M :=
  ⟨contract_isMinor M {e}, fun hM ↦ (hM.subset he).2 rfl⟩

lemma deleteElem_isStrictMinor (he : e ∈ M.E) : M ＼ e <m M :=
  ⟨delete_isMinor M {e}, fun hM ↦ (hM.subset he).2 rfl⟩

lemma isStrictMinor_iff_isMinor_contract_or_delete :
    N <m M ↔ ∃ e ∈ M.E, N ≤m M ／ e ∨ N ≤m M ＼ e := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨C, D, hC, hD, hCD, ⟨e,(heC | heD)⟩, rfl⟩ :=
      isStrictMinor_iff_exists_eq_contract_delete.1 h
    · refine ⟨e, hC heC, Or.inl ?_⟩
      rw [← insert_eq_of_mem heC, ← singleton_union, ← contract_contract, contractElem ]
      apply contract_delete_isMinor
    refine ⟨e, hD heD, Or.inr ?_⟩
    rw [contract_delete_comm _ hCD, ← insert_eq_of_mem heD, ← singleton_union, ← delete_delete]
    apply delete_contract_isMinor
  rintro ⟨e, he, (hc | hd)⟩
  · exact hc.trans_isStrictMinor (contractElem_isStrictMinor he)
  exact hd.trans_isStrictMinor (deleteElem_isStrictMinor he)

lemma IsMinor.isStrictMinor_or_eq (h : N ≤m M) : N <m M ∨ N = M := by
  rw [isStrictMinor_iff_isMinor_ne, and_iff_right h]
  exact ne_or_eq N M

lemma IsMinor.dual (h : N ≤m M) : N✶ ≤m M✶ := by
  obtain ⟨C, D, -, -, -, rfl⟩ := h
  rw [delete_dual_eq_dual_contract, contract_dual_eq_dual_delete]
  apply delete_contract_isMinor

lemma IsMinor.of_dual (h : N✶ ≤m M✶) : N ≤m M := by
  simpa using h.dual

lemma dual_isMinor_iff : N✶ ≤m M✶ ↔ N ≤m M :=
  ⟨IsMinor.of_dual, IsMinor.dual⟩

lemma isMinor_dual_iff_dual_isMinor : N ≤m M✶ ↔ N✶ ≤m M := by
  rw [← dual_isMinor_iff, dual_dual]

lemma IsStrictMinor.dual (h : N <m M) : N✶ <m M✶ := by
  rwa [IsStrictMinor, dual_isMinor_iff, dual_isMinor_iff]

lemma IsStrictMinor.of_dual (h : N✶ <m M✶) : N <m M := by
  simpa using h.dual

lemma dual_isStrictMinor_iff: N✶ <m M✶ ↔ N <m M :=
  ⟨IsStrictMinor.of_dual, IsStrictMinor.dual⟩

lemma isStrictMinor_dual_iff_dual_isStrictMinor : N <m M✶ ↔ N✶ <m M := by
  rw [← dual_isStrictMinor_iff, dual_dual]

lemma IsStrictMinor.encard_ground_lt [M.Finite] (hNM : N <m M) : N.E.encard < M.E.encard :=
  M.ground_finite.encard_lt_encard hNM.ssubset

/-- The scum theorem. We can always realize a minor by contracting an independent set and deleting
  a coindependent set -/
lemma IsMinor.exists_contract_indep_delete_coindep (h : N ≤m M) :
    ∃ C D, M.Indep C ∧ M.Coindep D ∧ Disjoint C D ∧ N = M ／ C ＼ D := by
  obtain ⟨C', D', hC', hD', hCD', rfl⟩ := h
  obtain ⟨I, hI⟩ := M.exists_isBasis C'
  obtain ⟨K, hK⟩ := M✶.exists_isBasis D'
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
  have hb : (M ／ C')✶.IsBasis K D' :=
    by
    rw [contract_dual_eq_dual_delete, delete_isBasis_iff, and_iff_right hK]
    exact hCD'.symm
  rw [← dual_dual (M ／ C' ＼ D'), delete_dual_eq_dual_contract, hb.contract_eq_contract_delete,
    hI.contract_eq_contract_delete, delete_dual_eq_dual_contract, contract_dual_eq_dual_delete,
    dual_dual, delete_delete, contract_delete_contract]
  rw [disjoint_union_right, and_iff_left disjoint_sdiff_left]
  exact disjoint_of_subset diff_subset diff_subset hCD'.symm

lemma IsMinor.exists_spanning_isRestriction_contract (h : N ≤m M) :
    ∃ C, M.Indep C ∧ (N ≤r M ／ C) ∧ (M ／ C).closure N.E = (M ／ C).E := by
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := h.exists_contract_indep_delete_coindep
  refine ⟨C, hC, delete_isRestriction _ _, ?_⟩
  rw [← (hD.coindep_contract_of_disjoint hCD.symm).closure_compl, delete_ground]

lemma IsMinor.exists_eq_contract_spanning_restrict (h : N ≤m M) :
    ∃ I R, M.Indep I ∧ Disjoint I R ∧ (M ／ I).Spanning R ∧ N = (M ／ I) ↾ R := by
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := h.exists_contract_indep_delete_coindep
  refine ⟨C, (M.E \ C) \ D, hC, disjoint_sdiff_right.mono_right diff_subset, ?_⟩
  rw [contract_spanning_iff, diff_diff_comm, diff_union_self, and_iff_left disjoint_sdiff_left,
    delete_eq_restrict, contract_ground, diff_diff_comm, and_iff_left rfl,
    union_eq_self_of_subset_right (subset_diff.2 ⟨hC.subset_ground, hCD⟩)]
  exact hD.compl_spanning

/-- Classically choose an independent contract-set from a proof that `N` is a isMinor of `M`. -/
def IsMinor.C (h : N ≤m M) : Set α :=
  h.exists_contract_indep_delete_coindep.choose

/-- Classically choose a coindependent delete-set from a proof that `N` is a isMinor of `M`. -/
def IsMinor.D (h : N ≤m M) : Set α :=
  h.exists_contract_indep_delete_coindep.choose_spec.choose

lemma IsMinor.C_indep (h : N ≤m M) : M.Indep h.C := by
  obtain ⟨-,h,-⟩ := h.exists_contract_indep_delete_coindep.choose_spec; exact h

lemma IsMinor.D_coindep (h : N ≤m M) : M.Coindep h.D := by
  obtain ⟨-,h,-⟩ := h.exists_contract_indep_delete_coindep.choose_spec.choose_spec; exact h

lemma IsMinor.disjoint (h : N ≤m M) : Disjoint h.C h.D := by
  obtain ⟨-,-,h,-⟩ := h.exists_contract_indep_delete_coindep.choose_spec.choose_spec; exact h

lemma IsMinor.eq_con_del (h : N ≤m M) : N = M ／ h.C ＼ h.D := by
  obtain ⟨-,-,-,h⟩ := h.exists_contract_indep_delete_coindep.choose_spec.choose_spec; exact h

lemma IsMinor.C_union_D_eq (h : N ≤m M) : h.C ∪ h.D = M.E \ N.E := by
  simp only [h.eq_con_del, delete_ground, contract_ground, diff_diff]
  rw [Set.diff_diff_cancel_left]
  exact union_subset h.C_indep.subset_ground h.D_coindep.subset_ground

lemma IsMinor.C_disjoint (h : N ≤m M) : Disjoint h.C N.E :=
  (subset_diff.1 h.C_union_D_eq.subset).2.mono_left subset_union_left

lemma IsMinor.D_disjoint (h : N ≤m M) : Disjoint h.D N.E :=
  (subset_diff.1 h.C_union_D_eq.subset).2.mono_left subset_union_right

lemma IsMinor.eq_con_restr (h : N ≤m M) : N = (M ／ h.C) ↾ N.E := by
  simp [h.eq_con_del, ← restrict_compl]

lemma IsStrictMinor.C_union_D_nonempty (h : N <m M) : (h.isMinor.C ∪ h.isMinor.D).Nonempty := by
  rw [h.isMinor.C_union_D_eq]
  exact nonempty_of_ssubset h.ssubset

lemma finite_setOf_isMinor (M : Matroid α) [M.Finite] : {N | N ≤m M}.Finite :=
  (finite_setOf_matroid M.ground_finite).subset (fun _ hNM ↦ hNM.subset)

end IsMinor

section Constructions

variable {E : Set α}

@[simp] lemma delete_ground_self (M : Matroid α) : M ＼ M.E = emptyOn α := by
  simp [← ground_eq_empty_iff]

@[simp] lemma contract_ground_self (M : Matroid α) : M ／ M.E = emptyOn α := by
  simp [← ground_eq_empty_iff]

@[simp] lemma emptyOn_isRestriction (M : Matroid α) : emptyOn α ≤r M :=
  ⟨∅, empty_subset _, by simp⟩

@[simp] lemma emptyOn_isMinor (M : Matroid α) : emptyOn α ≤m M :=
  M.emptyOn_isRestriction.isMinor

@[simp] lemma isMinor_emptyOn_iff : M ≤m emptyOn α ↔ M = emptyOn α :=
  ⟨fun h ↦ ground_eq_empty_iff.1 (eq_empty_of_subset_empty h.subset),
    by rintro rfl; apply emptyOn_isMinor⟩

@[simp] lemma isRestriction_emptyOn_iff : M ≤r emptyOn α ↔ M = emptyOn α := by
  refine ⟨fun h ↦ isMinor_emptyOn_iff.1 h.isMinor, ?_⟩
  rintro rfl
  exact IsRestriction.refl

@[simp] lemma loopyOn_delete (E X : Set α) : (loopyOn E) ＼ X = loopyOn (E \ X) := by
  rw [← restrict_compl, loopyOn_restrict, loopyOn_ground]

@[simp] lemma loopyOn_contract (E X : Set α) : (loopyOn E) ／ X = loopyOn (E \ X) := by
  simp_rw [eq_loopyOn_iff_closure, contract_closure_eq, empty_union, loopyOn_closure_eq,
    contract_ground, loopyOn_ground, true_and]

@[simp] lemma isMinor_loopyOn_iff : M ≤m loopyOn E ↔ M = loopyOn M.E ∧ M.E ⊆ E := by
  refine ⟨fun h ↦ ⟨by obtain ⟨C, D, _, _, _, rfl⟩ := h; simp, h.subset⟩, fun ⟨h, hss⟩ ↦ ?_⟩
  convert (loopyOn E).restrict_isMinor hss using 1
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
