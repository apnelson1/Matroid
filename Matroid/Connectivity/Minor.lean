import Matroid.Connectivity.Separation
import Matroid.Minor.Basic

open Set

namespace Matroid

variable {α : Type*} {M : Matroid α} {e f x y : α}

lemma ConnectedTo.delete_or_contract (hM : M.ConnectedTo x y) (hxe : x ≠ e) (hye : y ≠ e) :
    (M ＼ e).ConnectedTo x y ∨ (M ／ e).ConnectedTo x y := by
  obtain rfl | hne := eq_or_ne x y
  · simp  [hxe, hM.mem_ground_left]
  suffices (∀ C, M.Circuit C → e ∉ C → x ∈ C → y ∉ C) → ∃ C, (M ／ e).Circuit C ∧ x ∈ C ∧ y ∈ C by
    simpa [ConnectedTo, hne, deleteElem, - contractElem, or_iff_not_imp_left]
  intro h
  obtain ⟨C, hC, hxC, hyC⟩ := hM.exists_circuit_of_ne hne
  have heC : e ∈ C := by
    contrapose hyC
    exact h C hC hyC hxC
  refine ⟨C \ {e}, ?_, by simpa [hxe], by simpa [hye]⟩
  exact hC.contractElem_circuit (nontrivial_of_mem_mem_ne hxC hyC hne) heC

theorem Connected.delete_or_contract (hM : M.Connected) (hnt : M.E.Nontrivial) (e : α) :
    (M ＼ e).Connected ∨ (M ／ e).Connected := by

  simp only [connected_iff, deleteElem, ← ground_nonempty_iff, delete_ground, Set.mem_diff,
    Set.mem_singleton_iff, and_imp, contractElem, contract_ground, or_iff_not_imp_left, not_and,
    not_forall, Classical.not_imp, exists_and_left, exists_prop, true_implies, true_and,
    show (M.E \ {e}).Nonempty from hnt.exists_ne e, forall_exists_index, and_imp]

  intro f g hge hgE hfe hfE hnc x y hx hxe hy hye

  have hcon := ((hM.connectedTo f g).delete_or_contract hfe hge).resolve_left hnc

  have h' : ∀ z ∈ M.E, z ≠ e → (M ／ e).ConnectedTo z f ∨ (M ／ e).ConnectedTo z g := by
    refine fun z hz hze ↦ ?_
    contrapose! hnc
    have hzf := ((hM.connectedTo z f).delete_or_contract hze hfe).resolve_right hnc.1
    have hzg := ((hM.connectedTo z g).delete_or_contract hze hge).resolve_right hnc.2
    exact hzf.symm.trans hzg

  have h'' : ∀ z ∈ M.E, z ≠ e → (M ／ e).ConnectedTo z f :=
    fun z hz hze ↦ (h' z hz hze).elim id fun hzg ↦ hzg.trans hcon.symm

  exact (h'' x hx hxe).trans (h'' y hy hye).symm
