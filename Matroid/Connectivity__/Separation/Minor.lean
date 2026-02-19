import Matroid.Connectivity.Separation.Basic
import Matroid.Connectivity.Dual

open Set Function

variable {α : Type*} {M N : Matroid α} {j k : ℕ∞} {e f : α} {A B X X' Y Y' : Set α} {i b : Bool}
  {P : M.Separation} {C D : Set α} {e f : α}

namespace Matroid.Separation

@[simp, aesop unsafe 10% (rule_sets := [Matroid])]
lemma subset_ground_of_delete (P : (M ＼ D).Separation) (i : Bool) : P i ⊆ M.E :=
  P.subset_ground.trans diff_subset

@[simp, aesop unsafe 10% (rule_sets := [Matroid])]
lemma left_subset_ground_of_contract (P : (M ／ C).Separation) (i : Bool) : P i ⊆ M.E :=
  P.subset_ground.trans diff_subset

/-- Contract the elements of `C` to take a separation of `M` to a separation of `M ／ C`. -/
def contract (P : M.Separation) (C : Set α) : (M ／ C).Separation := P.induce diff_subset

@[simp, simp↓]
lemma contract_apply (P : M.Separation) (C : Set α) : (P.contract C) i = P i \ C := by
  simp only [contract, induce_apply, contract_ground]
  rw [← inter_diff_assoc, inter_eq_self_of_subset_left P.subset_ground]

@[simp, simp↓]
lemma contract_symm (P : M.Separation) (C : Set α) : (P.contract C).symm = P.symm.contract C := by
  simp [contract]

lemma contract_contract (P : M.Separation) (C₁ C₂ : Set α) :
    (P.contract C₁).contract C₂ = (P.contract (C₁ ∪ C₂)).copy (by simp) := by
  apply Separation.ext; simp [diff_diff]

lemma contract_congr (P : M.Separation) {C₁ C₂ : Set α} (h : C₁ ∩ M.E = C₂ ∩ M.E) :
    P.contract C₁ = (P.contract C₂).copy
      (by rw [← contract_inter_ground_eq, ← h, contract_inter_ground_eq]) := by
  have h1 := P.subset_ground (i := true)
  refine Separation.ext ?_;
  simp only [contract_apply, copy_apply]
  tauto_set

lemma contract_inter_ground (P : M.Separation) (C : Set α) :
    (P.contract (C ∩ M.E)) = (P.contract C).copy (by simp) :=
  P.contract_congr <| by simp [inter_assoc]

/-- Delete the elements of `D` to take a separation of `M` to a separation of `M ＼ D`. -/
def delete (P : M.Separation) (D : Set α) : (M ＼ D).Separation := P.induce diff_subset

@[simp, simp↓]
lemma delete_apply (P : M.Separation) (D : Set α) (i : Bool) : (P.delete D) i = P i \ D := by
  simp only [delete, induce_apply, delete_ground]
  rw [← inter_diff_assoc, inter_eq_self_of_subset_left P.subset_ground]

@[simp, simp↓]
lemma delete_symm (P : M.Separation) (D : Set α) : (P.delete D).symm = P.symm.delete D := by
  simp [delete]

lemma delete_delete (P : M.Separation) (D₁ D₂ : Set α) :
    (P.delete D₁).delete D₂ = (P.delete (D₁ ∪ D₂)).copy (by simp) := by
  apply Separation.ext; simp [diff_diff]

@[simp]
lemma contract_dual (P : M.Separation) (C : Set α) :
    (P.contract C).dual = (P.dual.delete C).copy (by simp) :=
  Separation.ext rfl

lemma dual_contract (P : M.Separation) (C : Set α) :
    P.dual.contract C = (P.delete C).dual.copy (by simp) :=
  Separation.ext rfl

@[simp]
lemma delete_dual (P : M.Separation) (D : Set α) :
    (P.delete D).dual = (P.dual.contract D).copy (by simp) :=
  Separation.ext rfl

lemma dual_delete (P : M.Separation) (D : Set α) :
    (P.delete D).dual = (P.dual.contract D).copy (by simp) :=
  Separation.ext rfl

lemma delete_congr (P : M.Separation) {D₁ D₂ : Set α} (h : D₁ ∩ M.E = D₂ ∩ M.E) :
    P.delete D₁ = (P.delete D₂).copy
      (by rw [← delete_inter_ground_eq, ← h, delete_inter_ground_eq]) := by
  have h2 := P.subset_ground (i := true)
  refine Separation.ext ?_
  simp only [delete_apply, copy_apply]
  tauto_set

lemma delete_inter_ground (P : M.Separation) (D : Set α) :
    (P.delete (D ∩ M.E)) = (P.delete D).copy (by rw [delete_inter_ground_eq]) :=
  P.delete_congr <| by simp [inter_assoc]

@[simp]
lemma disjoint_contract (P : (M ／ C).Separation) (i : Bool) : Disjoint (P i) C := by
  grw [P.subset_ground]
  exact disjoint_sdiff_left

@[simp]
lemma disjoint_delete (P : (M ＼ D).Separation) (i : Bool) : Disjoint (P i) D := by
  grw [P.subset_ground]
  exact disjoint_sdiff_left

@[simp]
lemma induce_eq_contract (P : M.Separation) (C : Set α) :
    (P.induce (M.contract_isMinor C).subset) = (P.contract C) := by
  refine Separation.ext ?_
  simp only [induce_apply, contract_ground, ↓contract_apply]
  grind [show P true ⊆ M.E from P.subset]

@[simp]
lemma induce_eq_delete (P : M.Separation) (D : Set α) :
    (P.induce (M.delete_isMinor D).subset) = (P.delete D) := by
  refine Separation.ext ?_
  simp only [induce_apply, delete_ground, ↓delete_apply]
  grind [show P true ⊆ M.E from P.subset]

@[simp]
lemma induce_eq_contract_delete (P : M.Separation) (C D : Set α) :
    (P.induce (M.contract_delete_isMinor C D).subset) = (P.contract C).delete D := by
  refine Separation.ext ?_
  simp only [induce_apply, delete_ground, contract_ground, ↓delete_apply, ↓contract_apply]
  grind [show P true ⊆ M.E from P.subset]

lemma contract_delete_comm (P : M.Separation) (hCD : Disjoint C D) :
    (P.contract C).delete D = ((P.delete D).contract C).copy (M.contract_delete_comm hCD).symm :=
  Separation.ext <| by simp [diff_diff_comm]

lemma delete_contract_comm (P : M.Separation) (hCD : Disjoint C D) :
    (P.delete D).contract C = ((P.contract C).delete D).copy (M.contract_delete_comm hCD) :=
  Separation.ext <| by simp [diff_diff_comm]

@[simps!]
abbrev contractDual (P : (M ／ C).Separation) : (M✶ ＼ C).Separation := P.dual.copy (by simp)

@[simps!]
abbrev deleteDual (P : (M ＼ D).Separation) : (M✶ ／ D).Separation := P.dual.copy (by simp)

def remove (P : M.Separation) (X : Set α) (b : Bool) : (M.remove X b).Separation :=
  P.induce ((M.remove_ground X b).trans_subset diff_subset)

@[simp]
lemma remove_true (P : M.Separation) (X : Set α) : P.remove X true = P.contract X := rfl

@[simp]
lemma remove_false (P : M.Separation) (X : Set α) : P.remove X false = P.delete X := rfl

lemma remove_apply (P : M.Separation) (X : Set α) (b i : Bool) : P.remove X b i = P i \ X := by
  cases b <;> simp

lemma remove_dual (P : M.Separation) (b : Bool) :
    (P.remove X b).dual = (P.dual.remove X (!b)).copy (by cases b <;> simp) :=
  Separation.ext <| by simp [remove_apply]

lemma remove_disjoint (P : M.Separation) {X : Set α} {b i} : Disjoint (P.remove X b i) X := by
  cases b <;> simp [disjoint_sdiff_left]

lemma remove_inter_ground (P : M.Separation) (X : Set α) (b : Bool) :
    P.remove (X ∩ M.E) b = (P.remove X b).copy (by simp) := by
  cases b
  · simp [delete_inter_ground]
  simp [contract_inter_ground]

lemma remove_congr (P : M.Separation) {X₁ X₂ : Set α} (h : X₁ ∩ M.E = X₂ ∩ M.E) (b : Bool) :
    P.remove X₁ b = (P.remove X₂ b).copy
      (by rw [← M.remove_inter_ground, ← h, M.remove_inter_ground]) := by
  cases b
  · simp [P.delete_congr h]
  simp [P.contract_congr h]

abbrev removeDual (P : (M.remove X b).Separation) : (M✶.remove X (!b)).Separation :=
  P.dual.copy (by simp)

@[simp]
lemma removeDual_true (P : (M.remove X true).Separation) : P.removeDual = P.contractDual := rfl

@[simp]
lemma removeDual_false (P : (M.remove X false).Separation) : P.removeDual = P.deleteDual := rfl

/-- Extend a separation `P` of some matroid `N
` to a matroid `M` with larger ground set by
adding the extra elements to side `b` of `P`. `-/
def ofGroundSubset (P : N.Separation) (hNM : N.E ⊆ M.E) (i : Bool) : M.Separation :=
  Bipartition.expand P hNM i

@[simp, simp↓]
lemma ofGroundSubset_apply (P : N.Separation) (hNM : N.E ⊆ M.E) (i j : Bool) :
    P.ofGroundSubset hNM j i = bif (i == j) then P i ∪ (M.E \ N.E) else P i := by
  simp [ofGroundSubset, Bipartition.expand_apply ..]

lemma ofGroundSubset_symm (P : N.Separation) (hNM : N.E ⊆ M.E) (i : Bool) :
    (P.ofGroundSubset hNM i).symm = P.symm.ofGroundSubset hNM (!i) :=
  Separation.ext <| by simp [ofGroundSubset_apply]

lemma ofSubset_apply_self (P : N.Separation) (hNM : N.E ⊆ M.E) (i : Bool) :
    P.ofGroundSubset hNM i i = P i ∪ (M.E \ N.E) := by
  simp

lemma ofSubset_apply_not (P : N.Separation) (hNM : N.E ⊆ M.E) (i : Bool) :
    P.ofGroundSubset hNM i (!i) = P (!i) := by
  simp

@[simp]
lemma ofSubset_not_apply (P : N.Separation) (hNM : N.E ⊆ M.E) (i : Bool) :
    P.ofGroundSubset hNM (!i) i = P i := by
  simp

@[simp, simp↓]
lemma ofGroundSubset_copy {N' : Matroid α} (P : N.Separation) (hN' : N = N') (hN'M : N'.E ⊆ M.E)
    (i : Bool) : (P.copy hN').ofGroundSubset hN'M i = P.ofGroundSubset (hN' ▸ hN'M) i :=
  Separation.ext_bool (i := !i) <| by simp

/-- Extend a separation of `M ／ C` to one of `M` by extending using side `b`. -/
def ofContract (P : (M ／ C).Separation) (i : Bool) : M.Separation := P.ofGroundSubset diff_subset i

@[simp, simp↓]
lemma ofContract_apply (P : (M ／ C).Separation) (hC : C ⊆ M.E := by aesop_mat) (i j : Bool) :
    P.ofContract i j = bif j == i then P j ∪ C else P j := by
  simp [ofContract, inter_eq_self_of_subset_right hC]

lemma ofContract_apply_self (P : (M ／ C).Separation) (hC : C ⊆ M.E := by aesop_mat) (i : Bool) :
    P.ofContract i i = P i ∪ C := by
  simp [P.ofContract_apply]

@[simp]
lemma ofContract_apply_not (P : (M ／ C).Separation) (i : Bool) : P.ofContract i (!i) = P !i := by
  simp [ofContract]

@[simp]
lemma ofContract_not_apply (P : (M ／ C).Separation) (i : Bool) : P.ofContract (!i) i = P i := by
  simpa using P.ofContract_apply_not (!i)

lemma ofContract_true_false (P : (M ／ C).Separation) : P.ofContract true false = P false :=
  P.ofContract_apply_not true

lemma ofContract_false_true (P : (M ／ C).Separation) : P.ofContract false true = P true :=
  P.ofContract_apply_not false

@[simp, simp↓]
lemma ofContract_symm (P : (M ／ C).Separation) (i : Bool) :
    (P.ofContract i).symm = P.symm.ofContract (!i) :=
  ofGroundSubset_symm ..

@[simp, simp↓]
lemma ofContract_copy {C' : Set α} (P : (M ／ C).Separation) (h_eq : M ／ C = M ／ C') (i : Bool) :
    (P.copy h_eq).ofContract i = P.ofContract i :=
  Separation.ext_bool (i := !i) <| by
    simp

/-- Extend a separation of `M ＼ D` to a separation of `M` by adding `D` to the left side. -/
def ofDelete (P : (M ＼ D).Separation) (i : Bool) : M.Separation := P.ofGroundSubset diff_subset i

lemma ofDelete_apply (P : (M ＼ D).Separation) (hD : D ⊆ M.E := by aesop_mat) (i j : Bool) :
    P.ofDelete i j = bif j == i then P j ∪ D else P j := by
  simp [ofDelete, inter_eq_self_of_subset_right hD]

@[simp]
lemma ofDelete_apply_self (P : (M ＼ D).Separation) (hD : D ⊆ M.E := by aesop_mat) (i : Bool) :
    P.ofDelete i i = P i ∪ D := by
  simp [P.ofDelete_apply]

lemma ofDelete_apply_self' (P : (M ＼ D).Separation) (i : Bool) :
    P.ofDelete i i = P i ∪ (D ∩ M.E) := by
  rw [ofDelete, ofGroundSubset_apply]
  simp [Set.inter_comm]

@[simp]
lemma ofDelete_apply_not (P : (M ＼ D).Separation) (i : Bool) : P.ofDelete i (!i) = P !i := by
  simp [ofDelete]

@[simp]
lemma ofDelete_not_apply (P : (M ＼ D).Separation) (i : Bool) : P.ofDelete (!i) i = P i := by
  simp [ofDelete]

@[simp]
lemma ofDelete_copy {D' : Set α} (P : (M ＼ D).Separation) (h_eq : M ＼ D = M ＼ D') (i : Bool) :
    (P.copy h_eq).ofDelete i = P.ofDelete i :=
  Separation.ext_bool (i := !i) <| by simp

lemma ofDelete_apply_superset (P : (M ＼ D).Separation) (i j : Bool) : P i ⊆ (P.ofDelete j) i := by
  obtain rfl | rfl := i.eq_or_eq_not j
  · grw [ofDelete_apply_self', ← subset_union_left]
  simp

@[simp]
lemma ofDelete_apply_diff (P : (M ＼ D).Separation) (i j : Bool) : P.ofDelete j i \ D = P i := by
  obtain rfl | rfl := i.eq_or_eq_not j
  · grw [P.ofDelete_apply_self']
    grind [subset_diff.1 <| P.subset (i := i)]
  simp

@[simp]
lemma ofDelete_symm (P : (M ＼ D).Separation) (i : Bool):
    (P.ofDelete i).symm = P.symm.ofDelete !i :=
  ofGroundSubset_symm ..

@[simp]
lemma ofDelete_dual (P : (M ＼ D).Separation) (i : Bool) :
    (P.ofDelete i).dual = P.deleteDual.ofContract i := rfl

@[simp]
lemma ofContract_dual (P : (M ／ C).Separation) (i : Bool) :
    (P.ofContract i).dual = P.contractDual.ofDelete i := rfl

@[simp]
lemma ofContract_contract (P : (M ／ C).Separation) (i : Bool) :
    (P.ofContract i).contract C = P :=
  Separation.ext_bool (!i) <| by simp

@[simp]
lemma ofDelete_delete (P : (M ＼ D).Separation) : (P.ofDelete i).delete D = P :=
  Separation.ext_bool (!i) <| by simp

lemma contract_ofContract (P : M.Separation) (hC : C ⊆ P i) : (P.contract C).ofContract i = P :=
  Separation.ext_bool (!i) <| by simp [(P.disjoint_bool i).symm.mono_right hC]

lemma delete_ofDelete (P : M.Separation) (hD : D ⊆ P i) : (P.delete D).ofDelete i = P :=
  Separation.ext_bool (!i) <| by simp [(P.disjoint_bool i).symm.mono_right hD]

/-- Extend a separation of `M.remove X b` to one of `M` by adding `X` to side `i`. -/
def ofRemove {b} (P : (M.remove X b).Separation) (i : Bool) : M.Separation :=
  ofGroundSubset P (by simp [diff_subset]) i

@[simp]
lemma ofRemove_false (P : (M.remove X false).Separation) : P.ofRemove = P.ofDelete := rfl

@[simp]
lemma ofRemove_true (P : (M.remove X true).Separation) : P.ofRemove = P.ofContract := rfl

@[simp]
lemma ofRemove_apply_self (P : (M.remove X b).Separation) (i : Bool)
    (hX : X ⊆ M.E := by aesop_mat) : P.ofRemove i i = P i ∪ X := by
  cases b
  · simp [P.ofDelete_apply_self]
  simp [P.ofContract_apply_self]

@[simp]
lemma ofRemove_apply_not (P : (M.remove X b).Separation) (i : Bool) :
    P.ofRemove i (!i) = P (!i) := by
  cases b <;> simp

lemma ofRemove_of_eq_true (P : (M.remove X b).Separation) (hb : b = true) :
    P.ofRemove i = (P.copy (M' := M ／ X) (by simp [hb])).ofContract i :=
  Separation.ext_bool (!i) <| by simp

lemma ofRemove_of_eq_false (P : (M.remove X b).Separation) (hb : b = false) :
    P.ofRemove i = (P.copy (M' := M ＼ X) (by simp [hb])).ofDelete i :=
  Separation.ext_bool (!i) <| by simp

@[simp]
lemma ofRemove_remove (P : (M.remove X b).Separation) : (P.ofRemove b).remove X b = P := by
  cases b <;> simp

lemma remove_ofRemove (P : M.Separation) (hX : X ⊆ P i) (b) : (P.remove X b).ofRemove i = P := by
  cases b
  · simp [P.delete_ofDelete hX]
  simp [P.contract_ofContract hX]

@[simp]
lemma ofRemove_dual {b} (P : (M.remove X b).Separation) :
    (P.ofRemove i).dual = P.removeDual.ofRemove i := by
  cases b <;> simp

lemma compl_delete (P : (M ＼ D).Separation) (hD : D ⊆ M.E := by aesop_mat) (i : Bool) :
    M.E \ P i = P (!i) ∪ D := by
  grw [← P.compl_eq, delete_ground, diff_diff_comm, diff_union_self, eq_comm, union_eq_left,
    subset_diff, and_iff_right hD, P.subset_ground]
  exact disjoint_sdiff_right

lemma compl_delete_not (P : (M ＼ D).Separation) (hD : D ⊆ M.E := by aesop_mat) (i : Bool) :
    M.E \ (P !i) = P i ∪ D := by
  simpa using P.compl_delete hD !i

lemma compl_contract (P : (M ／ C).Separation) (hC : C ⊆ M.E := by aesop_mat) (i : Bool) :
    M.E \ (P i) = P (!i) ∪ C :=  by
  simpa using (P.dual.copy (M.dual_contract C)).compl_delete hC i

lemma compl_contract_not (P : (M ／ C).Separation) (hC : C ⊆ M.E := by aesop_mat) (i : Bool) :
    M.E \ (P !i) = P i ∪ C := by
  simpa using P.compl_contract hC !i

@[simp]
lemma compl_union_contract (P : (M ／ C).Separation) (i : Bool) : M.E \ (P i ∪ C) = P !i := by
  rw [← P.compl_eq, Set.union_comm, contract_ground, diff_diff]

@[simp]
lemma compl_union_delete (P : (M ＼ D).Separation) (i : Bool) : M.E \ (P i ∪ D) = P !i := by
  rw [← P.compl_eq, Set.union_comm, delete_ground, diff_diff]

lemma compl_delete_singleton (P : (M ＼ {e}).Separation) (he : e ∈ M.E := by aesop_mat) (i : Bool) :
    M.E \ (P i) = insert e (P (!i)) := by
  rw [compl_delete, union_singleton]

lemma compl_contract_singleton (P : (M ／ {e}).Separation) (he : e ∈ M.E := by aesop_mat)
    (i : Bool) : M.E \ (P i) = insert e (P !i) := by
  rw [compl_contract, union_singleton]

lemma eConn_ofContract (P : (M ／ C).Separation) (i : Bool) :
    (P.ofContract i).eConn = P.eConn + M.eLocalConn (P !i) C := by
  wlog hCE : C ⊆ M.E generalizing C P with aux
  · simpa using aux (C := C ∩ M.E) (P.copy (by simp)) inter_subset_right
  rw [← (P.ofContract i).eConn_eq i, ofContract_apply_self,
    eConn_union_eq_eConn_contract_add _ (by simp), P.compl_union_contract, P.eConn_eq i]

lemma eConn_ofDelete (P : (M ＼ D).Separation) (i : Bool) :
    (P.ofDelete i).eConn = P.eConn + M✶.eLocalConn (P !i) D := by
  rw [← eConn_dual, ofDelete_dual, eConn_ofContract]
  simp

lemma eConn_ofDelete_ge (P : (M ＼ D).Separation) (i : Bool) :
    P.eConn ≤ (P.ofDelete i).eConn := by
  simp [eConn_ofDelete]

lemma eConn_ofDelete_le_eConn_add_eRelRk (P : (M ＼ D).Separation) (i : Bool) :
    (P.ofDelete i).eConn ≤ P.eConn + M.eRelRk (P i) (P i ∪ D) := by
  rw [P.eConn_eq_eLocalConn_of_isRestriction (delete_isRestriction M D) i,
    eConn_eq_eLocalConn _ i, ofDelete_apply_not, Separation.ofDelete, ofGroundSubset_apply]
  simp only [BEq.rfl, delete_ground, sdiff_sdiff_right_self, inf_eq_inter, cond_true]
  grw [eLocalConn_le_add_eRelRk_left _ subset_union_left, ← eRelRk_inter_ground_right,
    union_inter_distrib_right, inter_right_comm, inter_self, M.E.inter_comm,
    ← union_inter_distrib_right, eRelRk_inter_ground_right]

lemma eConn_ofDelete_eq_self_iff_of_coindep {P : (M ＼ D).Separation} (hPconn : P.eConn ≠ ⊤)
    (hD : M.Coindep D) : (P.ofDelete i).eConn = P.eConn ↔ D ⊆ M.closure (P i) := by
  rw [← eConn_eq _ i, ofDelete_apply_self, ← eConn_eq _ i, eq_comm,
    hD.delete_eConn_eq_union_iff' _ (by simpa)]
  grw [P.subset_ground]
  exact disjoint_sdiff_left

lemma eConn_ofDelete_le_self_iff_of_coindep {P : (M ＼ D).Separation} (hPconn : P.eConn ≠ ⊤)
    (hD : M.Coindep D) : (P.ofDelete i).eConn ≤ P.eConn ↔ D ⊆ M.closure (P i) := by
  rw [← eConn_ofDelete_eq_self_iff_of_coindep hPconn hD, eConn_ofDelete]
  simp

lemma eConn_induce_le_of_isMinor (P : M.Separation) (hNM : N ≤m M) :
    (P.induce hNM.subset).eConn ≤ P.eConn := by
  rw [← eConn_eq _ true, induce_apply, ← eConn_eq _ true, eConn_inter_ground]
  exact hNM.eConn_le _

lemma eConn_contract_le (P : M.Separation) (C : Set α) : (P.contract C).eConn ≤ P.eConn :=
  eConn_induce_le_of_isMinor P <| contract_isMinor ..

lemma eConn_delete_le (P : M.Separation) (D : Set α) : (P.delete D).eConn ≤ P.eConn :=
  eConn_induce_le_of_isMinor P <| delete_isMinor ..

lemma eConn_delete_le_of_subset (P : M.Separation) {X Y : Set α} (hXY : X ⊆ Y) :
    (P.delete Y).eConn ≤ (P.delete X).eConn := by
  have hrw := (congr_arg Separation.eConn <| P.delete_delete X (Y \ X)).symm.le
  grw [eConn_copy, (P.delete X).eConn_delete_le, union_diff_cancel hXY] at hrw
  assumption

lemma eConn_contract_le_of_subset (P : M.Separation) {X Y : Set α} (hXY : X ⊆ Y) :
    (P.contract Y).eConn ≤ (P.contract X).eConn := by
  grw [← eConn_dual, contract_dual, eConn_copy, eConn_delete_le_of_subset _ hXY,
    ← (P.contract X).eConn_dual, contract_dual, eConn_copy]

lemma eConn_eq_eConn_contract_add (P : M.Separation) (hC : C ⊆ P i) :
    P.eConn = (P.contract C).eConn + M.eLocalConn (P !i) C := by
  rw [← P.contract_ofContract hC, eConn_ofContract]
  rw [contract_apply, ofContract_contract, contract_ofContract _ hC, sdiff_eq_left.2]
  exact (P.disjoint_bool i).symm.mono_right hC

lemma eConn_le_eConn_contract_add (P : M.Separation) (C : Set α) :
    P.eConn ≤ (P.contract C).eConn + M.eRk C := by
  grw [P.eConn_eq_eConn_contract_add (C := C ∩ (P true)) inter_subset_right,
    eConn_eq_eConn_contract_add (C := C ∩ (P false)) (i := false), eLocalConn_le_eRk_right,
    eLocalConn_le_eRk_right, add_assoc, ← eRelRk_eq_eRk_contract, eRelRk_add_eRk_eq,
    ← inter_union_distrib_left, P.union_eq', eRk_inter_ground, contract_contract,
    P.contract_congr (by rw [← inter_union_distrib_left, P.union_eq]),
    P.contract_congr (C₂ := C) (by simp [inter_assoc])]
  · simp
  rw [P.contract_apply, ← P.compl_false]
  tauto_set

lemma eConn_le_eConn_delete_add (P : M.Separation) (D : Set α) :
    P.eConn ≤ (P.delete D).eConn + M✶.eRk D := by
  grw [← eConn_dual, eConn_le_eConn_contract_add _ D, dual_contract, eConn_copy, eConn_dual]

lemma eConn_ofContract_singleton_le_eConn_add_one (P : (M ／ {e}).Separation) (i : Bool) :
    (P.ofContract i).eConn ≤ P.eConn + 1 := by
  grw [eConn_ofContract, eLocalConn_le_eRk_right, eRk_singleton_le]

lemma eConn_ofDelete_singleton_le_eConn_add_one (P : (M ＼ {e}).Separation) (i : Bool) :
    (P.ofDelete i).eConn ≤ P.eConn + 1 := by
  grw [eConn_ofDelete, eLocalConn_le_eRk_right, eRk_singleton_le]

lemma eConn_eq_of_subset_closure_of_isRestriction {N : Matroid α} {Q : N.Separation}
    {P : M.Separation} (hNM : N ≤r M) (forall_subset : ∀ i, Q i ⊆ P i)
    (forall_subset_closure : ∀ i, P i ⊆ M.closure (Q i)) : P.eConn = Q.eConn := by
  rw [Separation.eConn, Separation.eConn,
    hNM.eLocalConn_eq_of_subset Q.subset_ground Q.subset_ground]
  refine le_antisymm ?_ <| M.eLocalConn_mono (forall_subset true) (forall_subset false)
  grw [← eLocalConn_closure_closure (X := Q _),
  M.eLocalConn_mono (forall_subset_closure true) (forall_subset_closure false)]

lemma eConn_ofDelete_eq_of_subset_closure (P : (M ＼ D).Separation) (j : Bool)
    (hD : D ⊆ M.closure (P j)) : (P.ofDelete j).eConn = P.eConn := by
  refine eConn_eq_of_subset_closure_of_isRestriction (by simp) (fun i ↦ ?_) (fun i ↦ ?_)
  · obtain rfl | rfl := i.eq_or_eq_not j
    · grw [ofDelete_apply_self, ← subset_union_left]
    simp
  obtain rfl | rfl := i.eq_or_eq_not j
  · rw [ofDelete_apply_self, union_subset_iff, and_iff_left hD]
    exact M.subset_closure _ <| P.subset_ground.trans diff_subset
  rw [ofDelete_apply_not]
  exact M.subset_closure _ <| P.subset_ground.trans diff_subset

lemma eConn_delete_eq_of_subset_of_subset_closure (P : M.Separation) (hD : D ⊆ P i)
    (hcl : D ⊆ M.closure (P i \ D)) : (P.delete D).eConn = P.eConn := by
  nth_rw 2 [← P.delete_ofDelete hD]
  rw [eConn_ofDelete_eq_of_subset_closure _ i (by simpa)]

lemma eConn_delete_eq_of_forall_subset_closure (hcl : ∀ i, D ∩ P i ⊆ M.closure (P i \ D)) :
    (P.delete D).eConn = P.eConn := by
  wlog hD : D ⊆ M.E generalizing D with aux
  · rw [← aux (D := D ∩ M.E) _ inter_subset_right, delete_inter_ground, eConn_copy]
    intro i
    grw [inter_right_comm, inter_subset_left, hcl, inter_subset_left]
  have h1 : (P.delete D).eConn = ((P.delete (D ∩ P true)).delete (D ∩ P false)).eConn := by
    simp_rw [Separation.delete_delete, eConn_copy]
    congr
    <;> simpa [← inter_union_distrib_left]
  rw [h1, eConn_delete_eq_of_subset_of_subset_closure (i := false),
    eConn_delete_eq_of_subset_of_subset_closure (i := true) _ inter_subset_right]
  · simpa using hcl true
  · rw [delete_apply, subset_diff, and_iff_right inter_subset_right]
    exact (disjoint_inter_left P).symm
  grw [delete_apply, delete_closure_eq, diff_diff, diff_diff, subset_diff,
    and_iff_left P.disjoint_inter_left.symm, ← union_assoc, union_right_comm, union_self,
    ← inter_union_distrib_left, P.union_eq, inter_eq_self_of_subset_left hD, hcl]

lemma eConn_delete_eq_eConn_iff_of_coindep (hP : P.eConn ≠ ⊤) (hD : M.Coindep D) :
    (P.delete D).eConn = P.eConn ↔ ∀ i, D ∩ P i ⊆ M.closure (P i \ D) := by
  refine ⟨fun h i ↦ ?_, eConn_delete_eq_of_forall_subset_closure⟩
  have h' : (P.delete (D ∩ P i)).eConn = P.eConn :=
    (P.eConn_delete_le _).antisymm <| by grw [← h, eConn_delete_le_of_subset _ inter_subset_left]
  nth_rw 1 [eq_comm, ← P.delete_ofDelete (D := D ∩ P i) inter_subset_right (i := i),
    eConn_ofDelete_eq_self_iff_of_coindep _ (hD.subset inter_subset_left)] at h'
  · simpa using h'
  grw [← lt_top_iff_ne_top, eConn_delete_le, lt_top_iff_ne_top]
  assumption

lemma eConn_le_eConn_delete_iff_of_coindep (hP : P.eConn ≠ ⊤) (hD : M.Coindep D) :
    P.eConn ≤ (P.delete D).eConn ↔ ∀ i, D ∩ P i ⊆ M.closure (P i \ D) := by
  rw [← eConn_delete_eq_eConn_iff_of_coindep hP hD, le_antisymm_iff, iff_and_self]
  exact fun _ ↦ eConn_delete_le ..

lemma eConn_contract_eq_self_of_forall_skew (hsk : ∀ i, M.Skew (P i) (C \ P i)) :
    (P.contract C).eConn = P.eConn := by
  rw [← P.eConn_eq true, ← Separation.eConn_eq _ true, contract_apply,
    (hsk true).eConn_contract_diff_eq_self_of_skew]
  exact (hsk false).mono (by simp) <| by grind [P.disjoint_false_true]

lemma eConn_contract_eq_eConn_iff_forall_skew (hP : (P.contract C).eConn ≠ ⊤)
    (hCE : C ⊆ M.E := by aesop_mat) :
    (P.contract C).eConn = P.eConn ↔ ∀ i, M.Skew (P i) (C \ P i) := by
  rw [← P.eConn_eq false, ← (P.contract C).eConn_eq false, contract_apply,
    eConn_contract_diff_eq_self_iff_skew_skew, Bool.forall_bool, P.compl_false,
    P.diff_eq_inter_bool true, Bool.not_true]
  rwa [← eConn_eq _ false, contract_apply] at hP

lemma eConn_le_eConn_contract_iff_forall_skew (hP : (P.contract C).eConn ≠ ⊤)
    (hCE : C ⊆ M.E := by aesop_mat) :
    P.eConn ≤ (P.contract C).eConn ↔ ∀ i, M.Skew (P i) (C \ P i) := by
  rw [← eConn_contract_eq_eConn_iff_forall_skew hP, le_antisymm_iff,
    and_iff_right (P.eConn_contract_le ..)]

lemma eConn_le_eConn_delete_iff_forall_skew (hP : (P.delete D).eConn ≠ ⊤)
    (hDE : D ⊆ M.E := by aesop_mat) :
    P.eConn ≤ (P.delete D).eConn ↔ ∀ i, M✶.Skew (P i) (D \ P i) := by
  rw [← P.eConn_dual, ← (P.delete D).eConn_dual, delete_dual, eConn_copy,
    eConn_le_eConn_contract_iff_forall_skew]
  · simp
  rwa [dual_contract, eConn_copy, eConn_dual]

/-- The generalized Bixby-Coullard inequality for pairs of separations. -/
lemma eConn_inter_add_eConn_inter_le_add (P : (M ／ X).Separation) (Q : (M ＼ X).Separation)
    (i : Bool) :
    M.eConn (P i ∩ Q i) + M.eConn (P (!i) ∩ Q (!i)) ≤ P.eConn + Q.eConn + M.eConn X := by
  wlog hX : X ⊆ M.E generalizing X P Q with aux
  · simpa using aux (X := X ∩ M.E) (P.copy (by simp)) (Q.copy (by simp)) inter_subset_right
  convert M.eConn_inter_add_eConn_union_union_le (C := P i) (D := Q i) (X := X) (by simp) (by simp)
    using 2
  · rw [union_assoc, X.union_comm, union_union_distrib_right, ← Q.compl_contract_not,
      ← P.compl_delete_not, dual_ground, ← diff_inter, eConn_compl]
  simp

/-- The Bixby-Coullard inequality for pairs of separations. -/
lemma eConn_inter_add_eConn_inter_le_add_of_singleton
    (P : (M ／ {e}).Separation) (Q : (M ＼ {e}).Separation) (i : Bool) :
    M.eConn (P i ∩ Q i) + M.eConn (P (!i) ∩ Q (!i)) ≤ P.eConn + Q.eConn + 1 := by
  grw [P.eConn_inter_add_eConn_inter_le_add, eConn_le_encard, encard_singleton]

/-- If `P` is a separation of a restriction of `M`, and each element of `M` is spanned by
one side of `P`, then `P` extends to a separation of `M` with the same connectivity. -/
lemma exists_of_isRestriction_of_forall_mem_closure (P : N.Separation) (hNM : N ≤r M)
    (h : ∀ e, M.IsNonloop e → ∃ i, e ∈ M.closure (P i)) : ∃ (Q : M.Separation),
    (∀ i, (P i ⊆ Q i ∧ M.closure (Q i) = M.closure (P i))) ∧ Q.eConn = P.eConn := by
  have h' (e : α) (he : e ∈ M.E) : ∃ i, e ∈ M.closure (P i) ∧ (e ∈ N.E → e ∈ P i) := by
    by_cases heN : e ∈ N.E
    · obtain ⟨i, hi⟩ := IndexedPartition.exists_mem P heN
      exact ⟨i, mem_closure_of_mem' _ hi he, fun _ ↦ hi⟩
    obtain hel | henl := M.isLoop_or_isNonloop e
    · exact ⟨true, hel.mem_closure (P true), by simp [heN]⟩
    simpa [heN] using h e henl
  choose! φ hφ using h'
  have aux {i} : P i ⊆ φ ⁻¹' {i} := fun e he ↦
    P.eq_of_mem_of_mem ((hφ _ (hNM.subset (P.subset_ground he))).2 (P.subset_ground he)) he
  have auxcl {i} : M.closure (φ ⁻¹' {i}) = M.closure (P i) := by
    refine (M.closure_subset_closure aux).antisymm' ?_
    rw [← M.closure_inter_ground, M.closure_subset_closure_iff_subset_closure]
    rintro x ⟨rfl, hxE⟩
    exact (hφ x hxE).1
  refine ⟨Separation.mk (fun i ↦ φ ⁻¹' {i} ∩ M.E) ?_ ?_, ?_⟩
  · simp +contextual [Pairwise, disjoint_left]
  · simp [← union_inter_distrib_right, ← preimage_union, subset_def]
  simp only [↓mk_apply, subset_inter_iff, aux, P.subset_ground.trans hNM.subset, and_self,
    closure_inter_ground, true_and]
  refine ⟨fun _ ↦ auxcl, ?_⟩
  simp only [eConn_eq_eLocalConn_true_false, ↓mk_apply, eLocalConn_inter_ground_right,
    eLocalConn_inter_ground_left]
  rw [hNM.eLocalConn_eq_of_subset, ← M.eLocalConn_closure_closure, auxcl, auxcl,
    eLocalConn_closure_closure]

/-- If `N` simplifies `M`, then each separation of `N` extends naturally to one of `M`. -/
lemma exists_of_simplifies (P : N.Separation) (hNM : N ≤si M) : ∃ (Q : M.Separation),
    (∀ i, (P i ⊆ Q i ∧ M.closure (Q i) = M.closure (P i))) ∧ Q.eConn = P.eConn := by
  refine P.exists_of_isRestriction_of_forall_mem_closure hNM.isRestriction fun e he ↦ ?_
  obtain ⟨f, hfN, hef⟩ := hNM.exists_of_isNonloop he
  obtain ⟨i, hi⟩ := P.exists_mem hfN
  use i
  grw [← singleton_subset_iff.2 hi]
  exact hef.mem_closure
