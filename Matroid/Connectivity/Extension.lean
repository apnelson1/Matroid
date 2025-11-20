import Matroid.Connectivity.Minor

variable {α ι : Type*} {M : Matroid α} {e f x y : α} {C D : Set α}

namespace Matroid

open Set

section Extension

variable {ι : Type*}

lemma ModularCut.multiconn_add_eq_multiConn_projectBy_add (U : M.ModularCut)
    (X : ι → Set α) [DecidablePred (· ∈ U)] (hU : U ≠ ⊤) :
    M.multiConn X + (if M.closure (⋃ i, X i) ∈ U then 1 else 0) =
        (M.projectBy U).multiConn X + {a | M.closure (X a) ∈ U}.encard := by
  classical
  wlog hXE : ∀ i, X i ⊆ M.E generalizing X with aux
  · convert aux (fun i ↦ X i ∩ M.E) (fun i ↦ inter_subset_right) using 2 with i
    · rw [multiConn_inter_ground]
    · simp [← iUnion_inter]
    · exact multiConn_inter_ground_congr <| by simp [inter_assoc]
    simp
  wlog h : ∃ e, e ∉ M.E generalizing α M X U with aux
  · have ho := Option.some_injective α
    specialize aux (U.map _ ho.injOn) (by simpa) (fun i ↦ .some '' X i) (fun i ↦ image_mono (hXE i))
      ⟨none, by simp⟩
    rw [multiConn_map_image _ _ _ (by simpa), U.projectBy_map, multiConn_map_image _ _ _ (by simpa),
      ← image_iUnion] at aux
    simp_rw [map_closure_eq, preimage_image_eq _ ho,
      U.image_mem_map_iff _ _ (closure_subset_ground ..)] at aux
    assumption
  obtain ⟨e, he⟩ := h
  have heX : e ∉ ⋃ i, X i := by simpa using fun i ↦ notMem_subset (hXE i) he
  have heX' (i) : e ∉ X i := by simpa using notMem_subset (hXE i) he
  nth_rw 1 [← U.extendBy_contractElem he,  ← U.extendBy_deleteElem he,
    multiConn_delete_of_disjoint _ (fun i ↦ disjoint_singleton_right.2 (notMem_subset (hXE i) he)),
    ← multiConn_project_eq_multiConn_contract, ENat.encard_eq_tsum_ite, eq_comm]
  convert (M.extendBy e U).multiConn_project_add_tsum_eLocalConn_eq X {e} with i
  · rw [eLocalConn_comm, IsNonloop.eLocalConn_eq_ite (by simpa), mem_closure_extendBy_iff _ he,
      or_iff_right (heX' i)]
    simp
  rw [eLocalConn_comm, IsNonloop.eLocalConn_eq_ite (by simpa), mem_closure_extendBy_iff _ he,
    or_iff_right heX]
  simp

/-- The formula relating the dual connectivity and the dual connectivity for the projection
by a modular cut. -/
lemma ModularCut.multiconn_dual_add_eq_multiConn_projectBy_dual_add (U : M.ModularCut)
    (X : ι → Set α) [DecidablePred (· ∈ U)] (hU : U ≠ ⊥) :
    M✶.multiConn X + {a | M.closure (M.E \ X a) ∉ U}.encard =
        (M.projectBy U)✶.multiConn X + (if M.closure (M.E \ (⋃ i, X i)) ∈ U then 0 else 1) := by
  classical
  wlog hXE : ∀ i, X i ⊆ M.E generalizing X with aux
  · convert aux (fun i ↦ X i ∩ M.E) (fun i ↦ inter_subset_right) using 2 with i
    · rw [← M.dual_ground, multiConn_inter_ground]
    · simp
    · exact multiConn_inter_ground_congr <| by simp [inter_assoc]
    simp [← iUnion_inter]
  wlog h : ∃ e, e ∉ M.E generalizing α M X U with aux
  · have ho := Option.some_injective α
    specialize aux (U.map _ ho.injOn) (by simpa) (fun i ↦ .some '' X i) (fun i ↦ image_mono (hXE i))
      ⟨none, by simp⟩
    rw [map_dual, multiConn_map_image _ _ _ (by simpa), U.projectBy_map, map_ground,
      map_dual, map_closure_eq, multiConn_map_image _ _ _ (by simpa)] at aux
    simp_rw [← image_iUnion, ← image_diff ho, map_closure_eq, preimage_image_eq _ ho,
      U.image_mem_map_iff _ _  (closure_subset_ground ..)] at aux
    exact aux
  obtain ⟨e, he⟩ := h
  nth_rw 1 [← U.extendBy_deleteElem he, ← U.extendBy_contractElem he, dual_delete, dual_contract,
    multiConn_delete_of_disjoint _ (fun i ↦ disjoint_singleton_right.2 (notMem_subset (hXE i) he)),
    ← multiConn_project_eq_multiConn_contract, eq_comm, ← ite_not]
  simp_rw [← U.mem_closure_extendBy_dual_iff he (hXE _),
      ← U.mem_closure_extendBy_dual_iff he (iUnion_subset hXE), eq_comm (a := _ + ite ..),
      ENat.encard_eq_tsum_ite, mem_setOf_eq]
  have hni : (M.extendBy e U)✶.Indep {e} := by
    rwa [indep_singleton, U.extendBy_isNonloop_dual_iff he]
  convert (M.extendBy e U)✶.multiConn_project_add_tsum_eLocalConn_eq (C := {e}) (X := X) with i <;>
  rw [eLocalConn_comm, IsNonloop.eLocalConn_eq_ite (by simpa using hni)]

lemma ModularCut.multiConn_dual_le_multiConn_projectBy_dual_add_one (U : M.ModularCut)
    (X : ι → Set α) : M✶.multiConn X ≤ (M.projectBy U)✶.multiConn X + 1 := by
  classical
  obtain rfl | hne := eq_or_ne U ⊥
  · simp
  have h_le := (U.multiconn_dual_add_eq_multiConn_projectBy_dual_add X hne).le
  grw [← le_self_add] at h_le
  grw [h_le, add_le_add_left]
  split_ifs <;> simp

lemma ModularCut.multiConn_dual_eq_multiConn_projectBy_dual_add_one_iff [Nonempty ι]
    (U : M.ModularCut) (X : ι → Set α) (hX : M✶.multiConn X ≠ ⊤) :
    M✶.multiConn X = (M.projectBy U)✶.multiConn X + 1 ↔
      M.closure (M.E \ ⋃ i, X i) ∉ U ∧ ∀ a, M.closure (M.E \ X a) ∈ U := by
  classical
  obtain rfl | hne := eq_or_ne U ⊥
  · simpa [eq_comm (a := M✶.multiConn X)] using hX.symm
  have h_eq := U.multiconn_dual_add_eq_multiConn_projectBy_dual_add X hne
  split_ifs at h_eq with h
  · simp only [add_zero] at h_eq
    rw [← h_eq, add_assoc, eq_comm]
    simpa [h]
  rw [← h_eq, eq_comm]
  simp [hX, h, eq_empty_iff_forall_notMem]

lemma ModularCut.multiConn_dual_eq_multiConn_projectBy_dual_add_one_iff' [Nonempty ι]
    (U : M.ModularCut) (X : ι → Set α) : M✶.multiConn X = (M.projectBy U)✶.multiConn X + 1 ↔
      (M✶.multiConn X = ⊤) ∨ (M.closure (M.E \ ⋃ i, X i) ∉ U ∧ ∀ a, M.closure (M.E \ X a) ∈ U) := by
  obtain htop | hnot := eq_or_ne (M✶.multiConn X) ⊤
  · simp only [htop, true_or, iff_true]
    grw [eq_comm, ← top_le_iff, ← htop]
    apply U.multiConn_dual_le_multiConn_projectBy_dual_add_one
  rw [U.multiConn_dual_eq_multiConn_projectBy_dual_add_one_iff _ hnot, or_iff_right hnot]

end Extension
