import Matroid.Loop
import Mathlib.Data.Matroid.Minor.Basic

open Set

variable {α : Type*} {M M' N : Matroid α} {e f : α} {I J R B X Y Z K S : Set α}

namespace Matroid

section Delete

variable {D D₁ D₂ R : Set α}

lemma eq_loopyOn_iff_closure {E : Set α} : M = loopyOn E ↔ M.loops = E ∧ M.E = E :=
  ⟨fun h ↦ by rw [h, loops]; simp, fun ⟨h,h'⟩ ↦
    by rw [← h', ← closure_empty_eq_ground_iff, ← loops, h, h']⟩

lemma IsRestriction.restriction_deleteElem (h : N ≤r M) (he : e ∉ N.E) : N ≤r M ＼ {e} :=
  h.restrict_delete_of_disjoint (by simpa)

lemma Loopless.delete (h : M.Loopless) (D : Set α) : (M ＼ D).Loopless := by
  simp [loopless_iff_loops]

instance [h : M.Loopless] {D : Set α} : (M ＼ D).Loopless :=
  h.delete D

lemma removeLoops_eq_delete (M : Matroid α) : M.removeLoops = M ＼ M.loops := by
  rw [← restrict_compl, removeLoops]
  convert rfl using 2
  simp [Set.ext_iff, mem_setOf, isNonloop_iff, isLoop_iff, mem_diff, and_comm]

lemma removeLoops_del_eq_removeLoops (h : X ⊆ M.loops) :
    (M ＼ X).removeLoops = M.removeLoops := by
  rw [removeLoops_eq_delete, delete_delete, removeLoops_eq_delete, loops, delete_closure_eq,
    empty_diff, union_diff_self, closure_empty, union_eq_self_of_subset_left h]

end Delete

section Contract

variable {C C₁ C₂ : Set α}

@[simp] lemma contract_ground (M : Matroid α) (C : Set α) : (M ／ C).E = M.E \ C := rfl

instance contract_finite [M.Finite] : (M ／ C).Finite := by
  rw [← dual_delete_dual]
  infer_instance

@[aesop unsafe 10% (rule_sets := [Matroid])]
lemma contract_ground_subset_ground (M : Matroid α) (C : Set α) : (M ／ C).E ⊆ M.E :=
  (M.contract_ground C).trans_subset diff_subset

lemma contractElem_eq_self (he : e ∉ M.E) : M ／ {e} = M := by
  rw [← dual_delete_dual, deleteElem_eq_self (by simpa), dual_dual]

lemma contract_eq_self_iff : M ／ C = M ↔ Disjoint C M.E := by
  rw [← dual_delete_dual, ← dual_inj, dual_dual, delete_eq_self_iff, dual_ground]

@[simp] lemma contract_empty (M : Matroid α) : M ／ ∅ = M := by
  rw [← dual_delete_dual, delete_empty, dual_dual]

lemma contract_contract_diff (M : Matroid α) (C₁ C₂ : Set α) :
    M ／ C₁ ／ C₂ = M ／ C₁ ／ (C₂ \ C₁) := by
  simp

lemma contract_eq_contract_iff : M ／ C₁ = M ／ C₂ ↔ C₁ ∩ M.E = C₂ ∩ M.E := by
  rw [← dual_delete_dual, ← dual_delete_dual, dual_inj,
    delete_eq_delete_iff, dual_ground]

@[simp] lemma contract_inter_ground_eq (M : Matroid α) (C : Set α) : M ／ (C ∩ M.E) = M ／ C := by
  rw [← dual_delete_dual, (show M.E = M✶.E from rfl), delete_inter_ground_eq]
  rfl

lemma coindep_contract_iff : (M ／ C).Coindep X ↔ M.Coindep X ∧ Disjoint X C := by
  rw [coindep_def, dual_contract, delete_indep_iff, ← coindep_def]

lemma Coindep.coindep_contract_of_disjoint (hX : M.Coindep X) (hXC : Disjoint X C) :
    (M ／ C).Coindep X :=
  coindep_contract_iff.mpr ⟨hX, hXC⟩

@[simp] lemma contract_isCocircuit_iff :
    (M ／ C).IsCocircuit K ↔ M.IsCocircuit K ∧ Disjoint K C := by
  rw [isCocircuit_def, dual_contract, delete_isCircuit_iff]

lemma Indep.contract_isBase_iff (hI : M.Indep I) :
    (M ／ I).IsBase B ↔ M.IsBase (B ∪ I) ∧ Disjoint B I := by
  rw [← dual_delete_dual, dual_isBase_iff', delete_ground, dual_ground, delete_isBase_iff,
    subset_diff, ← and_assoc, and_congr_left_iff, ← dual_dual M, dual_isBase_iff', dual_dual,
    dual_dual, union_comm, dual_ground, union_subset_iff, and_iff_right hI.subset_ground,
    and_congr_left_iff, ← isBase_restrict_iff, diff_diff, Spanning.isBase_restrict_iff,
    and_iff_left (diff_subset_diff_right subset_union_left)]
  · simp
  rwa [← dual_ground, ← coindep_iff_compl_spanning, dual_coindep_iff]

lemma Indep.contract_indep_iff (hI : M.Indep I) :
    (M ／ I).Indep J ↔ Disjoint J I ∧ M.Indep (J ∪ I) := by
  simp_rw [indep_iff, hI.contract_isBase_iff, union_subset_iff]
  exact ⟨fun ⟨B, ⟨hBI, hdj⟩, hJB⟩ ↦ ⟨disjoint_of_subset_left hJB hdj, _, hBI,
    hJB.trans subset_union_left, subset_union_right⟩,
    fun ⟨hdj, B, hB, hJB, hIB⟩ ↦ ⟨B \ I,⟨by simpa [union_eq_self_of_subset_right hIB],
      disjoint_sdiff_left⟩, subset_diff.2 ⟨hJB, hdj⟩ ⟩⟩

lemma IsNonloop.contractElem_indep_iff (he : M.IsNonloop e) :
    (M ／ {e}).Indep I ↔ e ∉ I ∧ M.Indep (insert e I) := by
  simp [he.indep.contract_indep_iff]

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
  simp_rw [IsBasis, hI.contract_indep_iff, contract_ground, subset_diff,
    maximal_subset_iff, and_imp] at hB
  refine hB.1.1.1.2.isBasis_of_maximal_subset (union_subset_union_left _ hB.1.1.2)
    fun K hK hKJ hKX ↦ ?_
  have hmax := hB.1.2 (t := K \ I)
  simp [subset_diff, diff_subset_iff, union_comm I, hKX, hB.1.1.1,
    subset_union_left.trans hKJ, union_eq_self_of_subset_left] at hmax
  rw [union_subset_iff] at hKJ
  rw [hB.1.2 (t := K \ I) disjoint_sdiff_left (by simpa [diff_union_of_subset hKJ.2])
    (diff_subset_iff.2 (by rwa [union_comm])) (subset_diff.2 ⟨hKJ.1, hB.1.1.1.1⟩),
    diff_union_of_subset hKJ.2]

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

lemma contract_eq_delete_of_subset_coloops (hX : X ⊆ M.coloops) : M ／ X = M ＼ X := by
  refine ext_indep rfl fun I _ ↦ ?_
  rw [(M.coloops_indep.subset hX).contract_indep_iff, delete_indep_iff, and_comm,
    union_indep_iff_indep_of_subset_coloops hX]

lemma contract_eq_delete_of_subset_loops (hX : X ⊆ M.loops) : M ／ X = M ＼ X := by
  rw [← dual_inj, dual_contract, dual_delete, eq_comm, contract_eq_delete_of_subset_coloops]
  rwa [dual_coloops]

lemma IsBasis.contract_eq_contract_delete (hI : M.IsBasis I X) : M ／ X = M ／ I ＼ (X \ I) := by
  nth_rw 1 [← diff_union_of_subset hI.subset]
  rw [union_comm, ← contract_contract]
  refine contract_eq_delete_of_subset_loops fun e he ↦ ?_
  rw [← isLoop_iff, ← singleton_dep, hI.indep.contract_dep_iff,
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

/-- Contracting the closure of a set is the same as contracting the set,
and deleting the rest of its elements. -/
lemma contract_closure_eq_contract_delete (M : Matroid α) (C : Set α) :
    M ／ M.closure C = M ／ C ＼ (M.closure C \ C) := by
  wlog hCE : C ⊆ M.E with aux
  · rw [← M.contract_inter_ground_eq C, ← closure_inter_ground, aux _ _ inter_subset_right,
      diff_inter, diff_eq_empty.2 (M.closure_subset_ground _), union_empty]
  obtain ⟨I, hI⟩ := M.exists_isBasis C
  rw [hI.isBasis_closure_right.contract_eq_contract_delete, hI.contract_eq_contract_delete,
    delete_delete, union_comm, diff_union_diff_cancel (M.subset_closure C) hI.subset]

lemma exists_eq_contract_indep_delete (M : Matroid α) (C : Set α) :
    ∃ I D : Set α, M.IsBasis I (C ∩ M.E) ∧ D ⊆ (M ／ I).E ∧ D ⊆ C ∧ M ／ C = M ／ I ＼ D := by
  obtain ⟨I, hI⟩ := M.exists_isBasis (C ∩ M.E)
  use I, C \ I ∩ M.E, hI
  rw [contract_ground, and_iff_right (inter_subset_left.trans diff_subset), diff_eq,
    diff_eq, inter_right_comm, inter_assoc, and_iff_right inter_subset_right,
    ← contract_inter_ground_eq, hI.contract_eq_contract_delete, diff_eq, inter_assoc]

lemma Indep.of_contract (hI : (M ／ C).Indep I) : M.Indep I :=
  ((M.exists_isBasis' C).choose_spec.contract_indep_iff.1 hI).1.subset subset_union_left

instance contract_rankFinite [RankFinite M] : RankFinite (M ／ C) := by
  obtain ⟨B, hB⟩ := (M ／ C).exists_isBase
  refine ⟨B, hB, hB.indep.of_contract.finite⟩

instance contract_finitary [Finitary M] : Finitary (M ／ C) := by
  obtain ⟨J, hJ⟩ := M.exists_isBasis' C
  suffices h : (M ／ J).Finitary by
    rw [hJ.contract_eq_contract_delete]
    infer_instance
  exact ⟨fun I hI ↦ hJ.indep.contract_indep_iff.2  ⟨disjoint_left.2 fun e heI ↦
    ((hI {e} (by simpa) (by simp)).subset_ground rfl).2,
    indep_of_forall_finite_subset_indep _ fun K hK hKfin ↦
      (hJ.indep.contract_indep_iff.1 <| hI (K ∩ I)
      inter_subset_right (hKfin.inter_of_left _)).2.subset (by tauto_set)⟩⟩

@[simp] lemma contract_isLoop_iff_mem_closure : (M ／ C).IsLoop e ↔ e ∈ M.closure C ∧ e ∉ C := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' C
  rw [hI.contract_eq_contract_delete, delete_isLoop_iff, ← singleton_dep,
    hI.indep.contract_dep_iff, singleton_union, hI.indep.insert_dep_iff, hI.closure_eq_closure]
  by_cases heI : e ∈ I
  · simp [heI, hI.subset heI]
  simp [heI, and_comm]

@[simp]
lemma contract_loops_eq : (M ／ C).loops = M.closure C \ C := by
  simp [Set.ext_iff, ← isLoop_iff, contract_isLoop_iff_mem_closure]

@[simp]
lemma contract_closure_eq (M : Matroid α) (C X : Set α) :
    (M ／ C).closure X = M.closure (X ∪ C) \ C := by
  rw [← diff_union_inter (M.closure (X ∪ C) \ C) X, diff_diff, union_comm C, ← contract_loops_eq,
    union_comm X, ← contract_contract, contract_loops_eq, subset_antisymm_iff, union_subset_iff,
    and_iff_right diff_subset, ← diff_subset_iff]
  simp only [sdiff_sdiff_right_self, inf_eq_inter, subset_inter_iff, inter_subset_right, and_true]
  refine ⟨fun e ⟨he, he'⟩ ↦ ⟨mem_closure_of_mem' _ (.inr he') (mem_ground_of_mem_closure he).1,
    (closure_subset_ground _ _ he).2⟩, fun e ⟨⟨he, heC⟩, he'⟩ ↦
    mem_closure_of_mem' _ he' ⟨M.closure_subset_ground _ he, heC⟩⟩

lemma IsBasis.contract_isBasis_of_isBasis' (h : M.IsBasis I X) (hJC : M.IsBasis' J C)
    (h_ind : M.Indep (I \ C ∪ J)) : (M ／ C).IsBasis (I \ C) (X \ C) := by
  refine Indep.isBasis_of_subset_of_subset_closure ?_ (diff_subset_diff_left h.subset) ?_
  · rwa [hJC.contract_indep_diff_iff]
  simp only [contract_closure_eq, diff_union_self, closure_union_congr_left h.closure_eq_closure]
  exact diff_subset_diff_left (subset_closure_of_subset' _ subset_union_left)

lemma IsBasis'.contract_isBasis' (h : M.IsBasis' I X) (hJC : M.IsBasis' J C)
    (h_ind : M.Indep (I \ C ∪ J)) : (M ／ C).IsBasis' (I \ C) (X \ C) := by
  rw [isBasis'_iff_isBasis_inter_ground, contract_ground, ← diff_inter_distrib_right]
  exact h.isBasis_inter_ground.contract_isBasis_of_isBasis' hJC h_ind

lemma IsBasis.contract_isBasis (h : M.IsBasis I X) (hJC : M.IsBasis J C)
    (h_ind : M.Indep (I \ C ∪ J)) : (M ／ C).IsBasis (I \ C) (X \ C) :=
  h.contract_isBasis_of_isBasis' hJC.isBasis' h_ind

lemma IsBasis.contract_isBasis_of_disjoint (h : M.IsBasis I X) (hJC : M.IsBasis J C)
    (hdj : Disjoint C X) (h_ind : M.Indep (I ∪ J)) : (M ／ C).IsBasis I X := by
  have h' := h.contract_isBasis hJC
  rwa [(hdj.mono_right h.subset).sdiff_eq_right, hdj.sdiff_eq_right, imp_iff_right h_ind] at h'

lemma IsBasis'.contract_isBasis_of_indep (h : M.IsBasis' I X) (h_ind : M.Indep (I ∪ J)) :
    (M ／ J).IsBasis' (I \ J) (X \ J) :=
  h.contract_isBasis' (h_ind.subset subset_union_right).isBasis_self.isBasis' (by simpa)

lemma IsBasis.contract_isBasis_of_indep (h : M.IsBasis I X) (h_ind : M.Indep (I ∪ J)) :
    (M ／ J).IsBasis (I \ J) (X \ J) :=
  h.contract_isBasis (h_ind.subset subset_union_right).isBasis_self (by simpa)

lemma IsBasis.contract_isBasis_of_disjoint_indep (h : M.IsBasis I X) (hdj : Disjoint J X)
    (h_ind : M.Indep (I ∪ J)) : (M ／ J).IsBasis I X := by
  rw [← hdj.sdiff_eq_right, ← (hdj.mono_right h.subset).sdiff_eq_right]
  exact h.contract_isBasis_of_indep h_ind

lemma IsCircuit.contract_isCircuit (hK : M.IsCircuit K) (hC : C ⊂ K) :
    (M ／ C).IsCircuit (K \ C) := by
  suffices ∀ e ∈ K, e ∉ C → M.Indep (K \ {e} ∪ C) by
    simpa [isCircuit_iff_dep_forall_diff_singleton_indep, diff_diff_comm (s := K) (t := C),
    dep_iff, (hK.ssubset_indep hC).contract_indep_iff, diff_subset_diff_left hK.subset_ground,
    disjoint_sdiff_left, diff_union_of_subset hC.subset, hK.not_indep]
  exact fun e heK heC ↦ (hK.diff_singleton_indep heK).subset <| by
    simp [subset_diff_singleton hC.subset heC]

lemma IsCircuit.contractElem_isCircuit (hC : M.IsCircuit C) (hnt : C.Nontrivial) (heC : e ∈ C) :
    (M ／ {e}).IsCircuit (C \ {e}) :=
  hC.contract_isCircuit (ssubset_of_ne_of_subset hnt.ne_singleton.symm (by simpa))

lemma IsCircuit.contract_dep (hK : M.IsCircuit K) (hCK : Disjoint C K) : (M ／ C).Dep K := by
  obtain ⟨I, hI⟩ := M.exists_isBasis (C ∩ M.E)
  rw [← contract_inter_ground_eq, Dep, hI.contract_indep_iff,
    and_iff_left (hCK.mono_left inter_subset_left), contract_ground, subset_diff,
    and_iff_left (hCK.symm.mono_right inter_subset_left), and_iff_left hK.subset_ground]
  exact fun hi ↦ hK.dep.not_indep (hi.subset subset_union_left)

lemma IsCircuit.contract_dep_of_not_subset (hK : M.IsCircuit K) {C : Set α} (hKC : ¬ K ⊆ C) :
    (M ／ C).Dep (K \ C) := by
  have h' := hK.contract_isCircuit (C := C ∩ K) (inter_subset_right.ssubset_of_ne (by simpa))
  simp only [diff_inter_self_eq_diff] at h'
  have hwin := h'.contract_dep (C := C \ K) disjoint_sdiff_sdiff
  rwa [contract_contract, inter_union_diff] at hwin

lemma IsCircuit.contract_diff_isCircuit (hC : M.IsCircuit C) (hK : K.Nonempty) (hKC : K ⊆ C) :
    (M ／ (C \ K)).IsCircuit K := by
  simpa [inter_eq_self_of_subset_right hKC] using hC.contract_isCircuit (diff_ssubset hKC hK)

lemma IsCircuit.exists_subset_isCircuit_of_contract (hC : (M ／ K).IsCircuit C) :
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

  have hd := hC'.contract_dep_of_not_subset fun hC'I ↦ (hI.indep.subset hC'I).not_dep hC'.dep
  rw [← hC.1.eq_of_dep_subset hd (by simpa [diff_subset_iff, union_comm])]
  exact diff_subset

lemma Dep.of_contract (h : (M ／ C).Dep X) (hC : C ⊆ M.E := by aesop_mat) : M.Dep (C ∪ X) := by
  rw [Dep, and_iff_left (union_subset hC (h.subset_ground.trans diff_subset))]
  intro hi
  rw [Dep, (hi.subset subset_union_left).contract_indep_iff, union_comm,
    and_iff_left hi] at h
  exact h.1 (subset_diff.1 h.2).2

lemma IsBasis.diff_subset_loops_contract (hIX : M.IsBasis I X) : X \ I ⊆ (M ／ I).loops := by
  rw [diff_subset_iff, contract_loops_eq, union_diff_self,
    union_eq_self_of_subset_left (M.subset_closure I)]
  exact hIX.subset_closure

lemma contract_spanning_iff (hC : C ⊆ M.E := by aesop_mat) :
    (M ／ C).Spanning X ↔ M.Spanning (X ∪ C) ∧ Disjoint X C := by
  rw [spanning_iff, contract_closure_eq, contract_ground, spanning_iff, union_subset_iff,
    subset_diff, ← and_assoc, and_congr_left_iff, and_comm (a := X ⊆ _), ← and_assoc,
    and_congr_left_iff]
  refine fun hdj hX ↦ ⟨fun h ↦ ⟨?_, hC⟩, fun h ↦ by simp [h]⟩
  rwa [← union_diff_cancel (M.subset_closure_of_subset' subset_union_right hC), h,
    union_diff_cancel]

lemma contract_spanning_iff' :
    (M ／ C).Spanning X ↔ M.Spanning (X ∪ (C ∩ M.E)) ∧ Disjoint X C := by
  rw [← contract_inter_ground_eq, contract_spanning_iff, and_congr_right_iff]
  refine fun h ↦ ⟨fun hdj ↦ ?_, Disjoint.mono_right inter_subset_left⟩
  rw [← diff_union_inter C M.E, disjoint_union_right, and_iff_left hdj]
  exact disjoint_sdiff_right.mono_left (subset_union_left.trans h.subset_ground)

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
  rw [isCocircuit_def, dual_contract] at hK
  exact hK.of_delete

lemma IsCocircuit.delete_isCocircuit {D : Set α} (hK : M.IsCocircuit K) (hD : D ⊂ K) :
    (M ＼ D).IsCocircuit (K \ D) := by
  rw [isCocircuit_def, dual_delete]
  exact hK.isCircuit.contract_isCircuit hD

lemma IsCocircuit.delete_diff_isCocircuit {X : Set α} (hK : M.IsCocircuit K) (hXK : X ⊆ K)
    (hX : X.Nonempty) : (M ＼ (K \ X)).IsCocircuit X := by
  rw [isCocircuit_def, dual_delete]
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

lemma contract_delete_comm (M : Matroid α) {C D : Set α} (hCD : Disjoint C D) :
    M ／ C ＼ D = M ＼ D ／ C := by
  wlog hCE : C ⊆ M.E generalizing C with aux
  · rw [← contract_inter_ground_eq, aux (hCD.mono_left inter_subset_left) inter_subset_right,
      contract_eq_contract_iff, inter_assoc, delete_ground,
      inter_eq_self_of_subset_right diff_subset]
  rw [delete_eq_restrict, delete_eq_restrict, contract_ground, diff_diff_comm,
    restrict_contract_eq_contract_restrict _ (by simpa [hCE, subset_diff])]

/-- A version of `contract_delete_comm` without the disjointness hypothesis,
and hence a less simple RHS. -/
lemma contract_delete_comm' (M : Matroid α) (C D : Set α) : M ／ C ＼ D = M ＼ (D \ C) ／ C := by
  rw [contract_delete_diff, contract_delete_comm _ disjoint_sdiff_right]

lemma delete_contract_eq_diff (M : Matroid α) (D C : Set α) : M ＼ D ／ C = M ＼ D ／ (C \ D) := by
  rw [contract_eq_contract_iff, delete_ground, diff_inter_diff_right, diff_eq, diff_eq, inter_assoc]

/-- A version of `delete_contract_comm'` without the disjointness hypothesis,
and hence a less simple RHS. -/
lemma delete_contract_comm' (M : Matroid α) (D C : Set α) : M ＼ D ／ C = M ／ (C \ D) ＼ D := by
  rw [delete_contract_eq_diff, ← contract_delete_comm _ disjoint_sdiff_left]

/-- A version of `contract_delete_contract` without the disjointness hypothesis,
and hence a less simple RHS. -/
lemma contract_delete_contract' (M : Matroid α) (C D C' : Set α) :
    M ／ C ＼ D ／ C' = M ／ (C ∪ C' \ D) ＼ D := by
  rw [delete_contract_eq_diff, ← contract_delete_comm _ disjoint_sdiff_left, contract_contract]

lemma contract_delete_contract (M : Matroid α) (C D C' : Set α) (h : Disjoint C' D) :
    M ／ C ＼ D ／ C' = M ／ (C ∪ C') ＼ D := by rw [contract_delete_contract', sdiff_eq_left.mpr h]

/-- A version of `contract_delete_contract_delete` without the disjointness hypothesis,
and hence a less simple RHS. -/
lemma contract_delete_contract_delete' (M : Matroid α) (C D C' D' : Set α) :
    M ／ C ＼ D ／ C' ＼ D' = M ／ (C ∪ C' \ D) ＼ (D ∪ D') := by
  rw [contract_delete_contract', delete_delete]

lemma contract_delete_contract_delete (M : Matroid α) (C D C' D' : Set α) (h : Disjoint C' D) :
    M ／ C ＼ D ／ C' ＼ D' = M ／ (C ∪ C') ＼ (D ∪ D') := by
  rw [contract_delete_contract_delete', sdiff_eq_left.mpr h]

/-- A version of `delete_contract_delete` without the disjointness hypothesis,
and hence a less simple RHS. -/
lemma delete_contract_delete' (M : Matroid α) (D C D' : Set α) :
    M ＼ D ／ C ＼ D' = M ／ (C \ D) ＼ (D ∪ D') := by
  rw [delete_contract_comm', delete_delete]

lemma delete_contract_delete (M : Matroid α) (D C D' : Set α) (h : Disjoint C D) :
    M ＼ D ／ C ＼ D' = M ／ C ＼ (D ∪ D') := by
  rw [delete_contract_delete', sdiff_eq_left.mpr h]

/- `N` is a minor of `M` if `N = M ／ C ＼ D` for some `C` and `D`.
The definition itsef does not require `C` and `D` to be disjoint, or subsets of the ground set.
See `Matroid.IsMinor.exists_eq_contract_delete_disjoint` for the stronger conclusion. -/
def IsMinor (N M : Matroid α) : Prop := ∃ C D, N = M ／ C ＼ D

def IsStrictMinor (N M : Matroid α) : Prop :=
  IsMinor N M ∧ ¬IsMinor M N

infixl:50 " ≤m " => Matroid.IsMinor
infixl:50 " <m " => Matroid.IsStrictMinor

@[simp]
lemma contract_delete_isMinor (M : Matroid α) (C D : Set α) : M ／ C ＼ D ≤m M :=
  ⟨C, D, rfl⟩

lemma IsMinor.exists_eq_contract_delete_disjoint (h : N ≤m M) :
    ∃ (C D : Set α), C ⊆ M.E ∧ D ⊆ M.E ∧ Disjoint C D ∧ N = M ／ C ＼ D := by
  obtain ⟨C, D, rfl⟩ := h
  exact ⟨C ∩ M.E, (D ∩ M.E) \ C, inter_subset_right, diff_subset.trans inter_subset_right,
    disjoint_sdiff_right.mono_left inter_subset_left, by
    simp [delete_eq_delete_iff, inter_assoc, inter_diff_assoc]⟩

lemma Indep.of_isMinor (hI : N.Indep I) (hNM : N ≤m M) : M.Indep I := by
  obtain ⟨C,D, rfl⟩ := hNM
  exact hI.of_delete.of_contract

lemma IsNonloop.of_isMinor (h : N.IsNonloop e) (hNM : N ≤m M) : M.IsNonloop e := by
  obtain ⟨C, D, rfl⟩ := hNM
  exact h.of_delete.of_contract

lemma IsLoop.of_isMinor (he : M.IsLoop e) (heN : e ∈ N.E) (hNM : N ≤m M) : N.IsLoop e := by
  rw [← not_isNonloop_iff]
  exact fun hnl ↦ he.not_isNonloop <| hnl.of_isMinor hNM

lemma IsMinor.eq_of_ground_subset (h : N ≤m M) (hE : M.E ⊆ N.E) : M = N := by
  obtain ⟨C, D, rfl⟩ := h
  rw [delete_ground, contract_ground, subset_diff, subset_diff] at hE
  rw [← contract_inter_ground_eq, hE.1.2.symm.inter_eq, contract_empty, ← delete_inter_ground_eq,
    hE.2.symm.inter_eq, delete_empty]

lemma IsMinor.subset (h : N ≤m M) : N.E ⊆ M.E := by
  obtain ⟨C, D, rfl⟩ := h; exact diff_subset.trans diff_subset

lemma IsMinor.refl {M : Matroid α} : M ≤m M := ⟨∅, ∅, by simp⟩

lemma IsMinor.trans {M₁ M₂ M₃ : Matroid α} (h : M₁ ≤m M₂) (h' : M₂ ≤m M₃) : M₁ ≤m M₃ := by
  obtain ⟨C₁, D₁, rfl⟩ := h
  obtain ⟨C₂, D₂, rfl⟩ := h'
  simp [contract_delete_contract_delete']

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
  obtain ⟨C, D, rfl⟩ := h
  infer_instance

lemma IsMinor.finitary (h : N ≤m M) [Finitary M] : Finitary N := by
  obtain ⟨C, D, rfl⟩ := h
  infer_instance

lemma IsMinor.le (h : N ≤m M) : N ≤ M := h

lemma IsStrictMinor.lt (h : N <m M) : N < M := h

@[simp]
lemma le_eq_isMinor : (fun M M' : Matroid α ↦ M ≤ M') = Matroid.IsMinor := rfl

@[simp]
lemma lt_eq_isStrictMinor : (fun M M' : Matroid α ↦ M < M') = Matroid.IsStrictMinor := rfl

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
  rw [isStrictMinor_iff_isMinor_ssubset]
  refine ⟨fun ⟨h, hss⟩ ↦ ?_, ?_⟩
  · obtain ⟨C, D, hC, hD, hdj, rfl⟩ := h.exists_eq_contract_delete_disjoint
    have hne : (M.E ∩ (C ∪ D)).Nonempty := by simpa [diff_diff] using hss
    exact ⟨C, D, hC, hD, hdj, hne.mono inter_subset_right, rfl⟩
  rintro ⟨C, D, hC, hD, hdj, hne, rfl⟩
  simp only [delete_ground, contract_ground, diff_diff, diff_ssubset_left_iff]
  rw [inter_eq_self_of_subset_right (union_subset hC hD)]
  exact ⟨⟨C, D, rfl⟩, hne⟩

lemma contract_isMinor (M : Matroid α) (C : Set α) : M ／ C ≤m M := by
  rw [← (M ／ C).delete_empty]
  apply contract_delete_isMinor

lemma contract_isMinor_of_subset (M : Matroid α) {C C' : Set α} (hCC' : C ⊆ C') :
    M ／ C' ≤m M ／ C := by
  rw [← diff_union_of_subset hCC', union_comm, ← contract_contract]
  apply contract_isMinor

lemma contract_isMinor_of_mem (M : Matroid α) {C : Set α} (he : e ∈ C) :
    M ／ C ≤m M ／ {e} :=
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

lemma contractElem_isStrictMinor (he : e ∈ M.E) : M ／ {e} <m M :=
  ⟨contract_isMinor M {e}, fun hM ↦ (hM.subset he).2 rfl⟩

lemma deleteElem_isStrictMinor (he : e ∈ M.E) : M ＼ {e} <m M :=
  ⟨delete_isMinor M {e}, fun hM ↦ (hM.subset he).2 rfl⟩

lemma isStrictMinor_iff_isMinor_contract_or_delete :
    N <m M ↔ ∃ e ∈ M.E, N ≤m M ／ {e} ∨ N ≤m M ＼ {e} := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨C, D, hC, hD, hCD, ⟨e,(heC | heD)⟩, rfl⟩ :=
      isStrictMinor_iff_exists_eq_contract_delete.1 h
    · refine ⟨e, hC heC, Or.inl ?_⟩
      rw [← insert_eq_of_mem heC, ← singleton_union, ← contract_contract]
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
  rw [dual_delete, dual_contract]
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

lemma IsStrictMinor.encard_ground_lt [N.Finite] (hNM : N <m M) : N.E.encard < M.E.encard :=
  N.ground_finite.encard_lt_encard hNM.ssubset

/-- The scum theorem. We can always realize a minor by contracting an independent set and deleting
  a coindependent set -/
lemma IsMinor.exists_contract_indep_delete_coindep (h : N ≤m M) :
    ∃ C D, M.Indep C ∧ M.Coindep D ∧ Disjoint C D ∧ N = M ／ C ＼ D := by
  obtain ⟨C', D', hC', hD', hCD', rfl⟩ := h.exists_eq_contract_delete_disjoint
  obtain ⟨I, hI⟩ := M.exists_isBasis C'
  obtain ⟨K, hK⟩ := M✶.exists_isBasis D'
  have hIK : Disjoint I K := disjoint_of_subset hI.subset hK.subset hCD'
  use I ∪ D' \ K, C' \ I ∪ K
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hss : (D' \ K) \ I ⊆ (M✶ ／ K ＼ I).loops := by
      rw [delete_loops_eq];
      exact diff_subset_diff_left hK.diff_subset_loops_contract
    rw [← dual_delete, ← dual_contract, dual_loops] at hss
    have hi := (coloops_indep _).subset hss
    rw [← contract_delete_comm _ hIK, delete_indep_iff, hI.indep.contract_indep_iff,
      diff_union_self, union_comm] at hi
    exact hi.1.2
  · rw [coindep_def]
    have hss : (C' \ I) \ K ⊆ (M ／ I ＼ K)✶.coloops := by
      rw [dual_coloops, delete_loops_eq]
      exact diff_subset_diff_left hI.diff_subset_loops_contract
    have hi := (coloops_indep _).subset hss
    rw [dual_delete, dual_contract, ←
      contract_delete_comm _ hIK.symm, delete_indep_iff, hK.indep.contract_indep_iff,
      diff_union_self] at hi
    exact hi.1.2
  · rw [disjoint_union_left, disjoint_union_right, disjoint_union_right,
      and_iff_right disjoint_sdiff_right, and_iff_right hIK, and_iff_left disjoint_sdiff_left]
    exact disjoint_of_subset diff_subset diff_subset hCD'.symm
  have hb : (M ／ C')✶.IsBasis K D' := by
    rwa [dual_contract, delete_isBasis_iff, and_iff_left hCD'.symm]
  rw [← dual_dual (M ／ C' ＼ D'), dual_delete, hb.contract_eq_contract_delete,
    hI.contract_eq_contract_delete, dual_delete, dual_contract,
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
  simp_rw [eq_loopyOn_iff_closure, loops, contract_closure_eq, empty_union, loopyOn_closure_eq,
    contract_ground, loopyOn_ground, true_and]

@[simp] lemma isMinor_loopyOn_iff : M ≤m loopyOn E ↔ M = loopyOn M.E ∧ M.E ⊆ E := by
  refine ⟨fun h ↦ ⟨by obtain ⟨C, D, _, _, _, rfl⟩ := h; simp, h.subset⟩, fun ⟨h, hss⟩ ↦ ?_⟩
  convert (loopyOn E).restrict_isMinor hss using 1
  rw [h, loopyOn_ground, loopyOn_restrict]

lemma contract_eq_loopyOn_of_spanning {C : Set α} (h : M.Spanning C) :
    M ／ C = loopyOn (M.E \ C) := by
  rw [eq_loopyOn_iff_closure, contract_ground, and_iff_left rfl, contract_loops_eq, h.closure_eq]

@[simp] lemma freeOn_delete (E X : Set α) : (freeOn E) ＼ X = freeOn (E \ X) := by
  rw [← loopyOn_dual_eq, ← dual_contract, loopyOn_contract, loopyOn_dual_eq]

@[simp] lemma freeOn_contract (E X : Set α) : (freeOn E) ／ X = freeOn (E \ X) := by
  rw [← loopyOn_dual_eq, ← dual_delete, loopyOn_delete, loopyOn_dual_eq]

lemma restrict_indep_eq_freeOn (hI : M.Indep I) : M ↾ I = freeOn I := by
  refine ext_indep rfl (fun J _ ↦ ?_)
  simp only [restrict_ground_eq, restrict_indep_iff, freeOn_indep_iff, and_iff_right_iff_imp]
  exact hI.subset

lemma indep_iff_restrict_eq_freeOn : M.Indep I ↔ (M ↾ I = freeOn I) := by
  refine ⟨restrict_indep_eq_freeOn, fun h ↦ ?_⟩
  have h' := restrict_indep_iff (M := M) (I := I) (R := I)
  rwa [h, freeOn_indep_iff, iff_true_intro Subset.rfl, and_true, true_iff] at h'

lemma restrict_subset_loops_eq (hX : X ⊆ M.loops) : M ↾ X = loopyOn X := by
  refine ext_indep rfl (fun I hI ↦ ?_)
  simp only [restrict_indep_iff, loopyOn_indep_iff]
  use fun h ↦ h.1.eq_empty_of_subset_loops (h.2.trans hX)
  rintro rfl
  simp

end Constructions

end Matroid
