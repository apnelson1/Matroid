import Matroid.Connectivity.ConnSystem.Tangle
import Matroid.Connectivity.Separation.Tutte

open Set

namespace Matroid

variable {α R : Type*} {N M : Matroid α} {X Y S : Set α} {e f : α} {k : ℕ∞}

/-- The connectivity function on `ℕ∞` associated with a matroid. -/
@[simps E]
noncomputable def eConnSystem (M : Matroid α) : ConnSystem α ℕ∞ where
  E := M.E
  toFun := M.eConn
  toFun_inter_ground := by simp
  toFun_compl := by simp
  toFun_submod _ _ _ _ := M.eConn_submod ..

@[simp]
lemma eConnSystem_apply (M : Matroid α) (X : Set α) : M.eConnSystem X = M.eConn X := rfl

@[simp]
lemma Separation.eConnSystem_pConn_apply (P : M.Separation) :
    M.eConnSystem.pConn P = P.eConn := by
  simp [ConnSystem.pConn, P.eConn_eq true]

lemma IsMinor.eConnSystem_le (h : N ≤m M) : N.eConnSystem ≤ M.eConnSystem :=
  ⟨h.subset, h.eConn_le⟩

@[simp]
lemma eConnSystem_normal (M : Matroid α) : M.eConnSystem.Normal := by
  simp [ConnSystem.Normal]

@[simp]
lemma eConnSystem_unitary (M : Matroid α) : M.eConnSystem.Unitary :=
  ⟨M.eConnSystem_normal, fun e ↦ by grw [eConnSystem_apply, eConn_le_encard, encard_singleton]⟩

lemma TutteConnected.Entangled (h : M.TutteConnected (k + 1)) : M.eConnSystem.Entangled k := by
  refine fun j hjk ↦
  ⟨fun T T' ↦ ?_⟩
  refine Tangle.ext fun X hX ↦ ?_
  have hle : M.eConn X ≤ j := hX.conn_le
  obtain ⟨b, h'⟩ := h.exists_encard_eq (P := M.ofSetSep X true hX.subset_ground)
    (by simp only [eConn_ofSetSep]; enat_to_nat!; lia)
  have hsmall (T₀ : Tangle M.eConnSystem j) : T₀.Small ((M.ofSetSep X true hX.subset_ground) b) :=
    T₀.small_of_encard_le (by simp) (by enat_to_nat!) (by cases b <;> simp_all) (by simp)
  cases b
  · exact False.elim <| hX.compl_large.not_small (hsmall _)
  apply hsmall
