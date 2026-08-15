module

public import Matroid.Minor.Delete
public import Mathlib.Combinatorics.Matroid.Minor.Contract
public import Matroid.ForMathlib.Matroid.Constructions

@[expose] public section

variable {α : Type*} {M M' N : Matroid α} {e f : α} {I J R B C X Y Z K S : Set α}

open Set

namespace Matroid

@[simp] lemma freeOn_contract (E X : Set α) : (freeOn E) ／ X = freeOn (E \ X) := by
  rw [← loopyOn_dual_eq, ← dual_delete, loopyOn_delete, loopyOn_dual_eq]

@[simp]
lemma loopyOn_contract (E X : Set α) : (loopyOn E) ／ X = loopyOn (E \ X) := by
  rw [← dual_inj, dual_contract, loopyOn_dual_eq, freeOn_delete, loopyOn_dual_eq]

lemma contract_eq_loopyOn_of_spanning (h : M.Spanning C) : M ／ C = loopyOn (M.E \ C) := by
  rw [eq_loopyOn_iff_loops, contract_ground, and_iff_left rfl, contract_loops_eq, h.closure_eq]

@[simp] lemma contract_ground_self (M : Matroid α) : M ／ M.E = emptyOn α := by
  simp [← ground_eq_empty_iff]

set_option backward.isDefEq.respectTransparency false in
lemma contract_map {β : Type*} {M : Matroid α} {f : α → β} (hf : InjOn f M.E) {C : Set α}
    (hC : C ⊆ M.E) : (M ／ C).map f (hf.mono sdiff_subset) = (M.map f hf) ／ (f '' C) := by
  simp_rw [← M.dual_delete_dual C]
  rw [← map_dual, delete_map (by simpa) (by simpa), ← map_dual, ← dual_contract, dual_dual]

lemma contract_comap {β : Type*} (M : Matroid β) (f : α → β) {C : Set β} (hC : C ⊆ range f) :
    (M ／ C).comap f = M.comap f ／ (f ⁻¹' C) := by
  obtain ⟨C, rfl⟩ := subset_range_iff_exists_image_eq.1 hC
  exact ext_closure fun X ↦ by simp [image_union, image_preimage_image]

@[simp]
lemma sum_contract {α β : Type*} (M : Matroid α) (N : Matroid β) (C : Set (α ⊕ β)) :
    (M.sum N) ／ C = (M ／ .inl ⁻¹' C).sum (N ／ .inr ⁻¹' C) := by
  rw [← dual_inj, dual_contract, sum_dual, sum_delete, ← dual_contract, ← dual_contract, ← sum_dual]

lemma contract_closure_congr (h : M.closure X = M.closure Y) (C : Set α) :
    (M ／ C).closure X = (M ／ C).closure Y := by
  rw [contract_closure_eq, contract_closure_eq, closure_union_congr_left h]

lemma contract_codep_iff {C X : Set α} : (M ／ C).Codep X ↔ M.Codep X ∧ Disjoint X C := by
  rw [codep_def, dual_contract, delete_dep_iff, codep_def]

lemma contractElem_of_notMem_ground (he : e ∉ M.E) : M ／ {e} = M := by
  rw [← dual_delete_dual, deleteElem_of_notMem_ground (by simpa), dual_dual]

lemma contract_nonspanning_iff (hC : C ⊆ M.E := by aesop_mat) :
    (M ／ C).Nonspanning X ↔ M.Nonspanning (X ∪ C) ∧ Disjoint X C := by
  wlog hXC : X ⊆ (M ／ C).E generalizing X with aux
  · refine iff_of_false (fun h ↦ hXC h.subset_ground) fun ⟨h1, h2⟩ ↦ hXC <| subset_sdiff.2 ⟨?_, h2⟩
    grw [dual_ground, ← h1.subset_ground, ← subset_union_left]
  obtain ⟨hXE, hdj⟩ := subset_sdiff.1 hXC
  rw [and_iff_left hdj, nonspanning_iff, contract_spanning_iff, and_iff_left hdj, and_iff_left hXC,
    ← not_spanning_iff]

lemma contract_rankPos_iff (hC : C ⊆ M.E := by aesop_mat) :
    (M ／ C).RankPos ↔ M.Nonspanning C := by
  rw [rankPos_iff_empty_not_spanning, contract_spanning_iff, empty_union, and_iff_left (by simp),
    not_spanning_iff]

lemma Nonspanning.contract_rankPos (hC : M.Nonspanning C) : (M ／ C).RankPos := by
  rwa [contract_rankPos_iff]

lemma girth_le_girth_contract_add (M : Matroid α) (C : Set α) :
    M.girth ≤ (M ／ C).girth + M.eRk C := by
  wlog hC : M.Indep C generalizing C with aux
  · obtain ⟨I, hI⟩ := M.exists_isBasis' C
    grw [hI.contract_eq_contract_delete, ← girth_le_girth_delete, aux _ hI.indep, hI.eRk_eq_eRk]
  rw [hC.eRk_eq_encard]
  obtain ⟨E, h_eq⟩ | hpos := (M ／ C).exists_eq_freeOn_or_rankPos_dual
  · simp [h_eq]
  obtain ⟨K, hK, hKg⟩ := (M ／ C).exists_isCircuit_girth
  obtain ⟨K', hK'ss, hK'⟩ := (hC.contract_dep_iff.1 hK.dep).2.exists_isCircuit_subset
  grw [hK'.girth_le_card, ← hKg, ← encard_union_le, encard_le_encard hK'ss]

lemma Dep.contract_of_delete {D : Set α} (hX : (M ＼ X).Dep (D \ X)) : (M ／ X).Dep (D \ X) := by
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  rw [delete_dep_iff] at hX
  rw [hI.contract_dep_iff, and_iff_left disjoint_sdiff_right]
  exact hX.1.superset subset_union_left (union_subset hX.1.subset_ground hI.indep.subset_ground)

lemma Dep.contract_of_disjoint {D : Set α} (hD : M.Dep D) (hDC : Disjoint D C) :
    (M ／ C).Dep D := by
  have aux : (M ＼ C).Dep (D \ C) := by
    rwa [delete_dep_iff, and_iff_left disjoint_sdiff_left, hDC.sdiff_eq_left]
  exact hDC.sdiff_eq_left ▸ aux.contract_of_delete

lemma contract_eq_contract_delete_of_subset_closure (hXY : X ⊆ Y) (hYX : Y ⊆ M.closure X) :
    M ／ Y = M ／ X ＼ (Y \ X) := by
  obtain ⟨I, hIX⟩ := M.exists_isBasis' X
  have hIY : M.IsBasis I Y := hIX.isBasis_closure_right.isBasis_subset (hIX.subset.trans hXY) hYX
  rw [hIY.contract_eq_contract_delete, hIX.contract_eq_contract_delete, delete_delete,
    union_comm, sdiff_union_sdiff_cancel hXY hIX.subset]

/-- Contracting a set whose intersection with `D` is independent never turns a dependent set `D`
into an independent set. -/
lemma Dep.contract_of_indep {D : Set α} (hD : M.Dep D) (hI : M.Indep (D ∩ I)) :
    (M ／ I).Dep (D \ I) := by
  nth_rw 1 [← inter_union_sdiff I D, inter_comm, ← contract_contract]
  refine Dep.contract_of_disjoint ?_ disjoint_sdiff_sdiff
  rwa [hI.isBasis_self.contract_dep_iff, sdiff_union_inter, disjoint_comm,
    and_iff_left disjoint_sdiff_inter]

lemma Codep.of_contract (h : (M ／ C).Codep X) : M.Codep X :=
  (dual_contract _ _ ▸ h.dep_dual).of_delete

lemma Coindep.of_contract (h : (M ／ C).Coindep I) : M.Coindep I :=
  (dual_contract _ _ ▸ h.indep).of_delete

lemma Codep.of_delete {D : Set α} (h : (M ＼ D).Codep X) (hD : D ⊆ M.E := by aesop_mat) :
    M.Codep (X ∪ D) := by
  rw [← dep_dual_iff, dual_delete] at h
  exact union_comm _ _ ▸ h.of_contract

lemma Codep.restrict (hD : M.Codep X) (hXR : X ⊆ R) : (M ↾ R).Codep X := by
  rw [restrict_eq_delete_disjointSum_loopyOn, Codep]
  generalize_proofs h
  simp only [disjointSum_dual, dual_delete, loopyOn_dual_eq, disjointSum_dep_iff, contract_ground,
    dual_ground, _root_.sdiff_sdiff_right_self, inf_eq_inter, freeOn_ground, freeOn_not_dep,
    or_false]
  rw [inter_comm M.E, ← inter_assoc, and_iff_left (by grind), inter_eq_self_of_subset_left hXR,
    inter_eq_self_of_subset_left hD.subset_ground]
  exact hD.dep_dual.contract_of_disjoint (C := M.E \ R) (by grind)

lemma removeLoops_eq_contract (M : Matroid α) : M.removeLoops = M ／ M.loops := by
  rw [contract_eq_delete_of_subset_loops rfl.subset, removeLoops_eq_delete]

lemma removeColoops_eq_contract (M : Matroid α) : M.removeColoops = M ／ M.coloops := by
  rw [removeColoops, removeLoops_eq_delete, dual_delete, dual_dual, dual_loops]

lemma removeColoops_eq_delete (M : Matroid α) : M.removeColoops = M ＼ M.coloops := by
  rw [removeColoops, removeLoops_eq_contract, dual_contract, dual_dual, dual_loops]

lemma removeLoops_removeColoops_comm (M : Matroid α) :
    M.removeLoops.removeColoops = M.removeColoops.removeLoops := by
  rw [removeColoops_eq_delete, removeLoops_coloops_eq, removeLoops_eq_delete,
    removeLoops_eq_delete, removeColoops_loops_eq, removeColoops_eq_delete, delete_comm]

set_option backward.isDefEq.respectTransparency false in
lemma removeColoops_disjointSum (M : Matroid α) :
     M = M.removeColoops.disjointSum (freeOn M.coloops)
      (by simp [removeColoops_eq_delete, disjoint_sdiff_left]) := by
  rw! [← dual_inj, disjointSum_dual, freeOn_dual_eq, removeColoops_dual,
    coloops, ← M✶.removeLoops_disjointSum]
  rfl

lemma IsRestriction.contract (h : N ≤r M) (hC : C ⊆ N.E) : N ／ C ≤r M ／ C := by
  obtain ⟨R, hR, rfl⟩ := h
  exact ⟨R \ C, sdiff_subset_sdiff_left hR, by rwa [restrict_contract_eq_contract_restrict]⟩

lemma IsSpanningRestriction.contract (h : N ≤sr M) (hC : C ⊆ N.E) : N ／ C ≤sr M ／ C := by
  refine ⟨h.isRestriction.contract hC, ?_⟩
  rw [contract_spanning_iff (hC.trans h.subset), contract_ground, and_iff_left disjoint_sdiff_left,
    sdiff_union_self]
  exact h.spanning.superset subset_union_left <| union_subset h.subset <| hC.trans h.subset

lemma Nonspanning.of_contract (h : (M ／ C).Nonspanning X) : M.Nonspanning X := by
  have hX : X ⊆ M.E \ C := h.subset_ground
  rw [← (M ／ C).dual_dual, nonspanning_dual_iff (by simpa using h.subset_ground), dual_ground,
    dual_contract, contract_ground] at h
  exact (M.dual_dual ▸ M.dual_ground ▸ h.of_delete.nonspanning_compl_dual).subset <| by grind

lemma Cyclic.contract {A : Set α} (hA : M.Cyclic A) (C : Set α) : (M ／ C).Cyclic (A \ C) := by
  rw [cyclic_iff_forall_mem_closure_diff_singleton] at ⊢ hA
  intro e ⟨heA, heC⟩
  grw [sdiff_sdiff_comm, contract_closure_eq, sdiff_union_self, mem_sdiff, and_iff_left heC,
    ← subset_union_left]
  exact hA e heA

lemma IsCircuit.isCircuit_or_isCircuit_insert_of_contractElem (hC : (M ／ {e}).IsCircuit C) :
    M.IsCircuit C ∨ M.IsCircuit (insert e C) := by
  obtain ⟨C', hC', hCC', hC'e⟩ := hC.exists_subset_isCircuit_of_contract
  by_cases heC' : e ∈ C'
  · simp [show insert e C = C' by grind, hC']
  simp [show C = C' by grind, hC']

lemma IsCircuit.isCircuit_contract_of_union {X C} (h : M.IsCircuit (X ∪ C)) (hdj : Disjoint X C)
    (hne : C.Nonempty) : (M ／ X).IsCircuit C := by
  have hwin := h.contract_isCircuit (C := X) (subset_union_left.ssubset_of_ne ?_)
  · rwa [union_sdiff_cancel_left hdj.inter_eq.subset] at hwin
  rwa [Ne, eq_comm, union_eq_left, ← sdiff_eq_empty, hdj.sdiff_eq_right, ← Ne,
    ← nonempty_iff_ne_empty]

lemma IsCircuit.isCircuit_contractElem_of_insert {C} (h : M.IsCircuit (insert e C)) (he : e ∉ C)
    (hC : C.Nonempty) : (M ／ {e}).IsCircuit C :=
  (singleton_union ▸ h).isCircuit_contract_of_union (by simpa) hC

/-- If `e` is a nonloop of both `M` and `N`, and `M` and `N` agree after removing `e`
in both ways, then `M = N`. -/
lemma ext_contractElem_deleteElem (heM : M.IsNonloop e) (heN : N.IsNonloop e)
    (hc : M ／ {e} = N ／ {e}) (hd : M ＼ {e} = N ＼ {e}) : M = N := by
  have hE : M.E = N.E := by
    rw [← insert_sdiff_self_of_mem heM.mem_ground, ← delete_ground, hd, delete_ground,
      insert_sdiff_self_of_mem heN.mem_ground]
  refine ext_indep hE fun I hIE ↦ ?_
  by_cases heI : e ∈ I
  · have hi := congr_arg (fun M : Matroid α ↦ M.Indep (I \ {e})) hc
    simpa [heM.contractElem_indep_iff, heN.contractElem_indep_iff, insert_eq_of_mem heI] using hi
  simpa [heI] using congr_arg (fun M : Matroid α ↦ M.Indep I) hd

/-- A version of `ext_contractElem_deleteElem` with slightly weaker assumptions. -/
lemma ext_contractElem_deleteElem' (heM : e ∈ M.E) (heN : e ∈ N.E)
    (heMl : M.IsLoop e → N.IsNonColoop e) (heNl : N.IsLoop e → M.IsNonColoop e)
    (hc : M ／ {e} = N ／ {e}) (hd : M ＼ {e} = N ＼ {e}) : M = N := by
  wlog he : M.IsNonloop e → N.IsNonloop e generalizing M N with aux
  · simp only [Classical.not_imp, not_isNonloop_iff heN] at he
    rw [← dual_inj, aux (M := N✶) (N := M✶) heN heM (by simp [he.1])
      (by simp [(heNl he.2).not_isColoop])]
    · rw [← dual_inj, dual_contract_dual, dual_contract_dual, hd]
    rw [← dual_inj, dual_delete_dual, dual_delete_dual, hc]
    simp [heNl he.2]
  have hE : M.E = N.E := by
    rw [← insert_sdiff_self_of_mem heM, ← delete_ground, hd, delete_ground,
      insert_sdiff_self_of_mem heN]
  obtain helM | henlM := M.isLoop_or_isNonloop e
  · obtain helN | henlN := N.isLoop_or_isNonloop e
    · rw [← M.delete_restrict_ground_of_subset_loops (L := {e}) (by simpa), hd, hE,
        delete_restrict_ground_of_subset_loops (by simpa)]
    obtain ⟨B, hB⟩ := (heMl helM).exists_isBase_notMem
    refine False.elim <| (hB.1.insert_dep ⟨henlN.mem_ground, hB.2⟩).not_indep ?_
    rw [← disjoint_singleton_right, ← (heMl helM).coindep.delete_isBase_iff, ← hd,
      ← contract_eq_delete_of_subset_loops (by simpa), hc] at hB
    exact (henlN.contractElem_indep_iff.1 hB.indep).2
  rw [ext_contractElem_deleteElem henlM (he henlM) hc hd]
