-- Tutte's Triangle Lemma says that if T is a triangle of M,  a 3-connected matroid,
-- with at least 4 elements, and e and f are distinct elements of T such that M\e
-- and M\f both fail to be 3-connected, then then there is a triad T* of M such that
-- T* contains e and the intersection of T and T* has cardinality two.
-- This file contains the proof that the lemma holds in the case that
-- M\e,f is not connected (when M has at least 5 elements).

-- Type checks with the toml entries:

-- [[require]]
-- name = "mathlib"
-- scope = "leanprover-community"
-- rev = "v4.27.0-rc1"

-- [[require]]
-- name = "Matroid"
-- git = "https://github.com/apnelson1/Matroid"
-- rev = "038d4db06185e42383e513372bdd4105d19a08ea"

import Mathlib.Logic.Function.Defs
import Mathlib.Combinatorics.Matroid.Basic
import Mathlib.Combinatorics.Matroid.Dual
import Mathlib.Combinatorics.Matroid.Circuit
import Mathlib.Combinatorics.Matroid.Minor.Contract
import Mathlib.Combinatorics.Matroid.Minor.Order
import Matroid.Connectivity.Basic
import Matroid.Connectivity.Tutte
import Matroid.Connectivity.Minor
import Matroid.Connectivity.Separation

open Set Matroid Function Separation

namespace Matroid

variable {i : Bool} {α : Type*} {e f g : α} {C K T X : Set α} {M : Matroid α} {P Q: M.Separation}

@[mk_iff]
structure IsTriangle (M : Matroid α) (T : Set α) : Prop where
  isCircuit : M.IsCircuit T
  three_elements : T.encard = 3

@[mk_iff]
structure IsTriad (M : Matroid α) (T : Set α) : Prop where
  isCocircuit : M.IsCocircuit T
  three_elements : T.encard = 3

lemma IsCocircuit.exists_subset_isCocircuit_of_delete (hC : (M ＼ K).IsCocircuit C) :
    ∃ C', M.IsCocircuit C' ∧ C ⊆ C' ∧ C' ⊆ C ∪ K := by
  have h : (M✶ ／ K).IsCircuit C := by
    rw [← dual_delete, ← IsCocircuit]
    exact hC
  apply IsCircuit.exists_subset_isCircuit_of_contract at h
  obtain ⟨C', hC'⟩ := h
  use C'

lemma IsCircuit.singleton_iff_dep (hXsing : X.encard = 1) : M.IsCircuit X ↔ M.Dep X := by
  rw [encard_eq_one] at hXsing
  obtain ⟨x, hx⟩ := hXsing
  apply Iff.intro
  apply IsCircuit.dep
  intro h₁
  rw [dep_iff_superset_isCircuit] at h₁
  obtain ⟨C, hC⟩ := h₁
  have h₂ : C ⊆ X := hC.1
  have h₃ : M.IsCircuit C := hC.2
  rw [hx, subset_singleton_iff_eq] at h₂
  have h₄ : C = ∅ → M.IsCircuit X := by
    intro h₅
    by_contra h₆
    have h₇ : C.Nonempty := h₃.nonempty
    rw [nonempty_iff_ne_empty] at h₇
    tauto
  have h₈ : C = {x} → M.IsCircuit X := by
    intro h₉
    rw [hx, ← h₉]
    exact hC.2
  apply Or.elim h₂ h₄ h₈

lemma IsCocircuit.singleton_iff_codep (hXsing : X.encard = 1) : M.IsCocircuit X ↔ M.Codep X := by
  apply Iff.intro
  intro h₁
  have h₂ : M✶.IsCircuit X := by
    rw [← IsCocircuit]
    exact h₁
  rw [IsCircuit.singleton_iff_dep, ← Codep] at h₂
  exact h₂
  exact hXsing
  intro h₃
  have h₄ : M✶.Dep X := by
    rw [← Codep]
    exact h₃
  rw [← IsCircuit.singleton_iff_dep, ← IsCocircuit] at h₄
  exact h₄
  exact hXsing

lemma IsTutteSeparation.ne_empty (hPtutte : P.IsTutteSeparation) (i : Bool): Nonempty (P i) ∧ Nonempty (P !i) := by
  by_contra hc
  simp only [not_and_or, not_nonempty_iff, isEmpty_coe_sort] at hc
  wlog h : (P i) = ∅ generalizing i
  apply this !i
  apply Or.resolve_left at hc
  apply hc at h
  tauto
  tauto
  have h₁ : M.Indep (P i) ∧ M.Coindep (P i) := by
    rw [h]
    simp only [empty_indep, true_and]
  have h₂ : ∃ i, M.Indep (P i) ∧ M.Coindep (P i) := by
    use i
  rw [← not_isTutteSeparation_iff_exists] at h₂
  tauto

lemma IsTutteSeparation.singleton_is_circuit_or_cocircuit (hPtutte : P.IsTutteSeparation) (i : Bool) (hPtruesing : (P i).encard = 1) : M.IsCircuit (P i) ∨ M.IsCocircuit (P i) := by
  have h₁ : M.Dep (P i) ∨ M.Codep (P i) := by
      rw [isTutteSeparation_iff i] at hPtutte
      exact hPtutte.1
  have h₄ : M.Dep (P i) → (M.IsCircuit (P i) ∨ M.IsCocircuit (P i)) := by
    intro h
    apply IsCircuit.singleton_iff_dep at hPtruesing
    rw [← hPtruesing] at h
    apply Or.inl
    exact h
  have h₅ : M.Codep (P i) → (M.IsCircuit (P i) ∨ M.IsCocircuit (P i)) := by
    intro h
    apply IsCocircuit.singleton_iff_codep at hPtruesing
    rw [← hPtruesing] at h
    apply Or.inr
    exact h
  apply Or.elim h₁ h₄ h₅

lemma IsConnected.nontrivial_of_loopless (hc : M.Connected) (hn : M.E.Nontrivial) : M.Loopless := by
  by_contra hc
  simp only [loopless_iff] at hc
  rw [← ne_eq, ← nonempty_iff_ne_empty, nonempty_def] at hc
  obtain ⟨l, hl⟩ := hc
  have h₁ : l ∈ M.E := by
    apply hl
    simp_all only [empty_inter, empty_subset, and_true, mem_setOf_eq, ground_isFlat]
  simp only [nontrivial_iff_pair_subset] at hn
  obtain ⟨x, y, hxy⟩ := hn
  wlog h₂ : x ≠ l generalizing x y
  apply this y x
  have h₃ : y ≠ x := by
    tauto
  have h₄ : {x, y} ⊆ M.E := hxy.2
  have h₅ : {y, x} ⊆ M.E := by
    simp only [insert_subset_iff, singleton_subset_iff, and_comm]
    nth_rewrite 2 [← singleton_subset_iff]
    rw [← insert_subset_iff]
    exact h₄
  apply And.intro h₃ h₅
  simp only [ne_eq, not_not] at h₂
  rw [← h₂]
  tauto
  have h₆ : {x, y} ⊆ M.E := hxy.2
  have h₇ : x ∈ M.E := by
    simp_all only [insert_subset_iff]
  rw [connected_iff] at hc
  have h₈ : ∀ ⦃e f : α⦄, e ∈ M.E → f ∈ M.E → M.ConnectedTo e f := hc.2
  apply h₈ at h₁
  apply h₁ at h₇
  unfold ConnectedTo at h₇
  by_cases h₉ : l = x ∧ l ∈ M.E
  have h₁₀ : l = x := h₉.1
  tauto
  simp only [h₉, false_or] at h₇
  obtain ⟨C, hC⟩ := h₇
  rw [← isLoop_iff] at hl
  have h₁₁ : M.IsCircuit {l} := by
    rw [singleton_isCircuit]
    exact hl
  have h₁₂ : M.IsCircuit C := hC.1
  apply IsCircuit.eq_of_subset_isCircuit at h₁₁
  apply h₁₁ at h₁₂
  have h₁₃ : {l} ⊆ C := by
    simp only [singleton_subset_iff]
    exact hC.2.1
  apply h₁₂ at h₁₃
  have h₁₄ : x ∈ C := by
    exact hC.2.2
  rw [← h₁₃] at h₁₄
  simp only [mem_singleton_iff] at h₁₄
  tauto

lemma Set.third_mem (hT : T.encard = 3) (he : e ∈ T) (hf : f ∈ T) (hef : e ≠ f) : ∃ g ∈ T, g ≠ e ∧ g ≠ f ∧ T = {e,f,g} := by
    have h₂ : {e,f} ⊆ T := (by simp [pair_subset_iff, he, hf])
    have h₃ : ({e,f} : Set α ) ≠ T := by
      by_contra! hc
      have h₄ : ({e,f} : Set α).encard = 3 := by
        rwa [hc]
      rw [encard_pair] at h₄
      tauto
      exact hef
    have h₆ : ({e,f} : Set α ) ⊂ T := by
      rw [ssubset_iff_subset_ne]
      simp only [h₂, true_and]
      exact h₃
    apply exists_of_ssubset at h₆
    obtain ⟨g, h₇⟩ := h₆
    use g
    simp only [h₇.1, true_and]
    have h₈ : g ∉ {e,f} := h₇.2
    have h₉ : g ≠ e := by
      simp only [mem_insert_iff, not_or] at h₈
      tauto
    have h₁₀ : g ≠ f := by
      simp only [mem_insert_iff, not_or] at h₈
      tauto
    simp [h₉, h₁₀]
    have h₁₁ : {e,f,g} ⊆ T := by
      simp [insert_subset_iff, he, hf, singleton_subset_iff, h₇.1]
    have h₁₂ : 3 = ({e,f,g} : Set α).encard := by
      symm
      rw [encard_eq_three]
      use e, f, g
      tauto
    have h₁₃ : ({e,f,g} : Set α).Finite := by
      rw [← encard_ne_top_iff, ← h₁₂]
      tauto
    have h₁₄ : T.encard ≤ ({e,f,g} : Set α).encard := by
      rw [← h₁₂, hT]
    by_contra hc
    have h₁₅ : ¬T ⊆ ({e,f,g} : Set α) := by
      by_contra hc₂
      rw [Subset.antisymm_iff, not_and_or] at hc
      by_cases hc₃ : ¬T ⊆ ({e,f,g} : Set α)
      tauto
      rw [or_iff_not_imp_left] at hc
      apply hc at hc₃
      tauto
    have h₁₆ : ({e,f,g} : Set α) ⊂ T := by
      simp only [ssubset_def, h₁₁, true_and]
      exact h₁₅
    apply Finite.encard_lt_encard at h₁₆
    rw [← h₁₂, hT] at h₁₆
    tauto
    exact h₁₃

-- lemma tutte_triangle_four_element (hG : 4 ≤ M.E.encard) (hM : M.TutteConnected 3) (he : e ∈ M.E) (hde : ¬((M＼{e}).TutteConnected 3)) : 4 < M.E.encard := by
--   sorry

lemma tutte_triangle_disconnected_case (hG : 4 < M.E.encard) (hM : M.TutteConnected 3) (hT : M.IsTriangle T) (he : e ∈ T) (hf : f ∈ T) (hef : e ≠ f) (hdef : ¬(M ＼ {e,f}).Connected) : ∃ K, (M.IsTriad K ∧ e ∈ K ∧ (K ∩ T).encard = 2) := by

  have heM : e ∈ M.E := by
    apply hT.isCircuit.subset_ground
    exact he
  have hfM : f ∈ M.E := by
    apply hT.isCircuit.subset_ground
    exact hf

-- There is an element g in T such that T = {e,f,g}.

  have hTcard : T.encard = 3 := hT.three_elements

  have h₁ : ∃ g ∈ T, g ≠ e ∧ g ≠ f ∧ T = {e,f,g} := by
    apply Set.third_mem at hTcard
    apply hTcard at he
    apply he at hf
    apply hf at hef
    exact hef
  obtain ⟨g, hg⟩ := h₁

  have hgM : g ∈ M.E := by
    apply mem_of_mem_of_subset
    refine hg.1
    refine hT.isCircuit.subset_ground

  have hgMdef : g ∈ (M ＼ {e,f}).E := by
    simp only [delete_ground, mem_diff, hgM, true_and, mem_insert_iff, not_or, mem_singleton_iff, hg.2, not_false_eq_true]

-- M\ e, f is nonempty and disconnected, so it contains a separation P.

  have h₂ : (M＼{e,f}).Nonempty := by
    simp only [← ground_nonempty_iff, delete_ground, diff_nonempty, not_subset_iff_exists_mem_notMem]
    use g
    simp only [hgM, true_and, mem_insert_iff, not_or, mem_singleton_iff]
    tauto
  apply tutteConnected_two_iff at h₂
  rw [← h₂, ← one_add_one_eq_two, not_tutteConnected_iff_exists] at hdef

  obtain ⟨P, hP⟩ := hdef

  have hPfalse : P false ⊆ (M ＼ {e,f}).E := P.subset_ground
  have hPtrue : P true ⊆ (M ＼ {e,f}).E := P.subset_ground
  have hPefalse : e ∉ P false := by
    by_contra hc
    apply mem_of_mem_of_subset at hc
    apply hc at hPfalse
    simp only [delete_ground, mem_diff, mem_insert_iff, true_or, not_true_eq_false, and_false] at hPfalse
  have hPetrue : e ∉ P true := by
    by_contra hc
    apply mem_of_mem_of_subset at hc
    apply hc at hPtrue
    simp only [delete_ground, mem_diff, mem_insert_iff, true_or, not_true_eq_false, and_false] at hPtrue
  have hPffalse : f ∉ P false := by
    by_contra hc
    apply mem_of_mem_of_subset at hc
    apply hc at hPfalse
    simp only [delete_ground, mem_diff, mem_insert_iff, mem_singleton_iff, or_true, not_true_eq_false, and_false] at hPfalse
  have hPftrue : f ∉ P true := by
    by_contra hc
    apply mem_of_mem_of_subset at hc
    apply hc at hPtrue
    simp only [delete_ground, mem_diff, mem_insert_iff, mem_singleton_iff, or_true, not_true_eq_false, and_false] at hPtrue

-- Without loss of generality, g is in (P false).

  wlog hgtrue : g ∈ P false generalizing P
  apply this P.symm
  simp only [eConn_symm, isTutteSeparation_symm_iff]
  exact hP
  simp only [Separation.symm_false]
  exact hPtrue
  simp only [Separation.symm_true]
  exact hPfalse
  simp only [Separation.symm_false]
  exact hPetrue
  simp only [Separation.symm_true]
  exact hPefalse
  simp only [Separation.symm_false]
  exact hPftrue
  simp only [Separation.symm_true]
  exact hPffalse
  simp only [Separation.symm_false]
  have hgtrue₁ : g ∈ (M ＼ {e,f}).E \ (P false) := by
    simp only [delete_ground, diff_diff, mem_diff, hgM, mem_union, not_or, hgtrue, not_false_eq_true, and_true, mem_insert_iff, hg.2.1, mem_singleton_iff, hg.2.2]
  rw [Separation.compl_eq] at hgtrue₁
  exact hgtrue₁

-- We consider the partition Q = (P true, P false ∪ {e,f}) of M.

  let QtoFun : Bool → Set α := fun i ↦ bif i then (P true) else ((P false) ∪ ({e,f} : Set α))

  have hQpartition₁ : Disjoint (P true) ((P false) ∪ {e,f}) := by
    have hQpartition₃ : Disjoint (P false) (P true) := P.disjoint_false_true
    have hQpartition₄ : (P true) ⊆ (M ＼ {e,f}).E := P.subset_ground
    have hQpartition₅ : Disjoint (P true) {e,f} := by
      by_contra hc
      simp only [disjoint_insert_right, not_and_or, hPetrue, not_not, false_or, disjoint_singleton_right] at hc
      tauto
    apply Disjoint.union_right
    exact P.disjoint_true_false
    exact hQpartition₅

  have hQpartitiondis : Pairwise (Disjoint on QtoFun) := by
    rw [pairwise_disjoint_on_bool]
    exact hQpartition₁

  have hQpartition₂ : (P true) ∪ ((P false) ∪ {e,f}) = M.E := by
    rw [subset_antisymm_iff]
    have hQpartition₆ : (P false) ⊆ M.E := by
      apply subset_trans
      refine P.subset_ground
      simp only [delete_ground, diff_subset]
    have hQpartition₇ : (P true) ⊆ M.E := by
      apply subset_trans
      refine P.subset_ground
      simp only [delete_ground, diff_subset]
    have hQpartition₈ : (P true) ∪ ((P false) ∪ {e,f}) ⊆ M.E := by
      simp only [union_subset_iff, hQpartition₇, insert_subset_iff, heM, singleton_subset_iff, hfM, and_true, hQpartition₆]
    have hQpartition₉ : (M ＼ {e,f}).E ⊆ ((P false) ∪ {e,f}) ∪ (P true) := by
      rw [← P.union_eq]
      simp only [union_subset_iff, subset_union_right]
      grw [← subset_union_left]
      simp only [subset_union_left, and_true]
    have hQpartition₁₀ : M.E = (M ＼ {e,f}).E ∪ {e,f} := by
      simp only [delete_ground, diff_union_self]
      rw [union_eq_self_of_subset_right]
      simp only [insert_subset_iff, heM, singleton_subset_iff, hfM, true_and]
    have hQpartition₁₁ : (P false) ∪ {e,f} ∪ (P true) = ((P false) ∪ (P true)) ∪ {e,f} := by
      simp only [union_assoc]
      nth_rewrite 2 [union_comm]
      rfl
    have hQpartition₁₂ : M.E ⊆ (P true) ∪ ((P false) ∪ {e,f}) := by
      rw [hQpartition₁₀, delete_ground, diff_union_self, union_insert, union_singleton, insert_eq_of_mem, insert_eq_of_mem, ← union_assoc]
      have hQpartition₁₃ : ⋃ i, P i = (M ＼ {e,f}).E := by
        simp only [P.iUnion_eq]
      have hQpartition₁₄ : ⋃ i, P i = (P true) ∪ (P false) := by
        simp only [iUnion_bool, Separation.union_eq]
      rw [← hQpartition₁₄, hQpartition₁₃, delete_ground]
      simp only [subset_diff_union]
      exact hfM
      simp only [mem_insert_iff, heM, or_true]
    apply And.intro hQpartition₈ hQpartition₁₂

  have hQpartitioniunion : ⋃ i, QtoFun i = M.E := by
    simp_all only [iUnion_bool, cond_true, cond_false, QtoFun]

  let Q : M.Separation := (Separation.mk QtoFun hQpartitiondis hQpartitioniunion)

  have hQtrue : Q true = P true := by rfl
  have hQleft : Q false = P false ∪ {e,f} := by rfl

-- Q is a 2-separation of M.

  have hQ2sep : Q.eConn + 1 ≤ 2 := by
    have hQ2sep₆ : M.eLocalConn (Q true) (M.closure (Q false \ {f})) + 1 ≤ 2 := by
      have hQ2sep₆₁ : M.eLocalConn (Q true) (Q false \ {f}) + 1 ≤ 2 := by
        have hQ2sep₆₂ : (M ＼ {f}).eLocalConn (Q true) (Q false \ {f}) + 1 ≤ 2 := by
          have hQ2sep₆₄ : (M ＼ {f}).eConn (Q true) + 1 ≤ 2 := by
            have hQ2sep₆₁₃ : (M ＼ {f} ＼ {e}).eConn (Q true) + 1 ≤ 1 := by
              simp only [delete_delete, union_singleton, hQtrue]
              simp only [eConn_eq]
              exact hP.1
            grw [eConn_le_eConn_delete_singleton_add_one]
            rw [← one_add_one_eq_two]
            simp only [ENat.add_one_le_add_one_iff]
            exact hQ2sep₆₁₃
          rw [eConn_eq_eLocalConn] at hQ2sep₆₄
          have hQ2sep₆₅ : ((M ＼ {f}).E \ Q true) = Q false \ {f} := by
            rw [hQleft, hQtrue, delete_ground]
            have hQ2sep₆₆ : P true  = (M.E \ {e,f}) \ (P false) := by
              rw [← delete_ground]
              rw [Separation.compl_eq]
              tauto
            rw [hQ2sep₆₆]
            simp only [diff_diff]
            have hQ2sep₆₇ : ({f} ∪ M.E \ ({e, f} ∪ P false)) = M.E \ (P false ∪ {e}) := by
              simp [union_singleton, ← diff_diff]
              rw [← delete_ground]
              simp only [Separation.compl_eq]
              have hQ2sep₆₁₁ : insert e (P false) = (Q false) \ {f} := by
                rw [hQleft]
                simp only [union_insert, union_singleton]
                rw [insert_comm]
                have hQ2sep₆₁₂ : f ∉ insert e (P false) := by
                  simp only [mem_insert_iff, not_or, hPffalse, not_false_eq_true, and_true]
                  tauto
                apply insert_diff_self_of_notMem at hQ2sep₆₁₂
                rw [hQ2sep₆₁₂]
              rw [hQ2sep₆₁₁]
              rw [diff_diff_eq_sdiff_union]
              nth_rewrite 1 [Separation.compl_eq]
              simp only [union_singleton]
              tauto
              simp only [singleton_subset_iff, hfM]
            rw [hQ2sep₆₇]
            rw [diff_diff_right_self]
            have hQ2sep₆₈ : (P false ∪ {e}) ⊆ M.E := by
              simp only [union_subset_iff, singleton_subset_iff, heM, and_true]
              apply subset_trans at hPfalse
              have hQ2sep₆₉ : (M ＼ {e,f}).E ⊆ M.E := by
                simp only [delete_ground, diff_subset]
              apply hPfalse at hQ2sep₆₉
              exact hQ2sep₆₉
            apply inter_eq_self_of_subset_right at hQ2sep₆₈
            rw [hQ2sep₆₈]
            simp only [union_singleton, union_insert]
            rw [insert_comm]
            have hQ2sep₆₁₀ : f ∉ insert e (P false) := by
              simp only [mem_insert_iff, hPffalse, or_false]
              rw [← not_ne_iff, not_not]
              tauto
            apply insert_diff_self_of_notMem at hQ2sep₆₁₀
            rw [hQ2sep₆₁₀]
          rw [← hQ2sep₆₅]
          exact hQ2sep₆₄
        rw [eLocalConn_delete_eq] at hQ2sep₆₂
        simp only [diff_diff, union_singleton, pair_eq_singleton] at hQ2sep₆₂
        have hQ2sep₆₃ : Q true = Q true \ {f} := by
          rw [diff_singleton_eq_self]
          rw [hQtrue]
          exact hPftrue
        rw [hQ2sep₆₃]
        exact hQ2sep₆₂
      rw [eLocalConn_closure_right]
      exact hQ2sep₆₁
    have hQ2sep₅ : Q false ⊆ M.closure (Q false \ {f}) := by
      have hQ2sep₅₁ : f ∈  M.closure (Q false \ {f}) := by
        rw [mem_closure_iff_mem_or_exists_isCircuit, mem_diff_singleton, hQleft]
        simp_all only [mem_union, mem_insert_iff, mem_singleton_iff, or_true, true_and]
        simp
        use T
        simp only [subset_insert_iff, mem_diff_singleton]
        rw [hg.2.2.2]
        simp only [diff_singleton_subset_iff, insert_subset_iff, mem_insert_iff, true_or, true_and, or_true, singleton_subset_iff, hgtrue, and_true]
        symm at hef
        simp_all only [ne_eq, not_false_eq_true, or_true]
        rw [← hg.2.2.2]
        simp_all only [hT.isCircuit, true_and]
      have hQ2sep₅₂ : Q false = (Q false \ {f}) ∪ {f} := by
        simp only [union_singleton, insert_diff_singleton]
        rw [hQleft]
        simp_all only [union_insert, union_singleton, insert_comm]
        simp only [mem_insert_iff, true_or, insert_eq_of_mem]
      nth_rewrite 1 [hQ2sep₅₂]
      simp only [union_subset_iff, singleton_subset_iff, hQ2sep₅₁, and_true]
      have hQ2sep₅₃ : Q false \ {f} ⊆ M.E := by
        simp only [diff_subset_iff, singleton_union]
        rw [insert_eq_of_mem]
        simp only [Separation.subset_ground]
        exact hfM
      apply subset_closure at hQ2sep₅₃
      exact hQ2sep₅₃
    have hQ2sep₄ : M.eLocalConn (Q true) (Q false) ≤  M.eLocalConn (Q true) (M.closure (Q false \ {f})) := by
      apply eLocalConn_mono_right at hQ2sep₅
      exact hQ2sep₅
    have hQ2sep₃ : M.eLocalConn (Q true) (Q false) + 1 ≤  M.eLocalConn (Q true) (M.closure (Q false \ {f})) + 1:= by
      grw [hQ2sep₄]
    have hQ2sep₂ : M.eLocalConn (Q true) (Q false) + 1 ≤ 2 := by
      grw [← hQ2sep₆]
      exact hQ2sep₃
    have hQ2sep₁ : M.eConn (Q true) + 1 ≤ 2 := by
      simp only [eConn_eq_eLocalConn]
      rw [Separation.compl_eq]
      exact hQ2sep₂
    rw [← eConn_eq]
    exact hQ2sep₁

-- Now Q true must contain a single element.

  have hQtruesing : (Q true).encard ≤ 1 := by
    have hQtruesing₁ : ¬Q.IsTutteSeparation := by
      by_contra hc
      have hQtruesing₂ : ∃ R : M.Separation, R.eConn + 1 ≤ 2 ∧ R.IsTutteSeparation := by
        use Q
      rw [← not_tutteConnected_iff_exists] at hQtruesing₂
      simp only [two_add_one_eq_three] at hQtruesing₂
      tauto
    rw [isTutteSeparation_iff true] at hQtruesing₁
    simp only [not_and_or] at hQtruesing₁
    have hQtruesing₃ : ∃ C ⊆ Q false, M.IsCircuit C := by
      use T
      simp only [hT.isCircuit, and_true]
      rw [hQleft, hg.2.2.2]
      simp only [insert_subset_iff, mem_union, mem_insert_iff, true_or, or_true, true_and, mem_singleton_iff, singleton_subset_iff, hgtrue]
    have hQtruesing₄ : M.Dep (Q false) := by
      rw [dep_iff_superset_isCircuit]
      use T
      simp only [hT.isCircuit, and_true]
      rw [hg.2.2.2]
      simp only [insert_subset_iff, hQleft, union_insert, mem_insert_iff, true_or, true_and, union_singleton, or_true, singleton_subset_iff, hgtrue]
    have hQtruesing₅ : (M.Dep (Q false) ∨ M.Codep (Q false)) := Or.inl hQtruesing₄
    have hQtruesing₆ : ¬(M.Dep (Q true) ∨ M.Codep (Q true)) := by
      tauto
    rw [not_or, not_dep_iff, not_codep_iff] at hQtruesing₆
    rw [← eConn_eq_encard_iff'] at hQtruesing₆
    rw [← one_add_one_eq_two, ENat.add_one_le_add_one_iff] at hQ2sep
    rw [← hQtruesing₆]
    rw [eConn_eq]
    exact hQ2sep
    simp only [eConn_eq]
    have hQtruesing₇ : Q.eConn ≤ 1 := by
      rw [← one_add_one_eq_two, ENat.add_one_le_add_one_iff] at hQ2sep
      exact hQ2sep
    apply ne_top_of_le_ne_top at hQtruesing₇
    exact hQtruesing₇
    symm
    apply ENat.top_ne_one
  have hQtruesing₈ : (Q true).encard = 1 := by
    rw [ENat.le_one_iff_eq_zero_or_eq_one] at hQtruesing
    have hQtruesing₉ : ¬(Q true).encard = 0 := by
      by_contra hc
      rw [encard_eq_zero, hQtrue] at hc
      have hQtruesing₁₀ : P.IsTutteSeparation := hP.2
      apply IsTutteSeparation.ne_empty at hQtruesing₁₀
      simp [hc] at hQtruesing₁₀
    apply Or.resolve_left at hQtruesing
    apply hQtruesing at hQtruesing₉
    exact hQtruesing₉

  -- (P true) is a circuit or a cocircuit of M \ e, f.

  have hPtutte : P.IsTutteSeparation := hP.2

  have hPtruecocorcir : (M ＼ {e,f}).IsCircuit (P true) ∨ (M ＼ {e,f}).IsCocircuit (P true) := by
    apply IsTutteSeparation.singleton_is_circuit_or_cocircuit at hPtutte
    rw [hQtrue] at hQtruesing₈
    apply hPtutte at hQtruesing₈
    exact hQtruesing₈

  -- (P true) must be a cocircuit of M \ e,f.

  have hPtruecoc₇ : (M ＼ {e,f}).IsCircuit (P true) → (M ＼ {e,f}).IsCocircuit (P true) := by
    have hPtruecoc₁ : M.Nonempty := by
      simp only [← ground_nonempty_iff, nonempty_def]
      use g
    have hPtruecoc₂ : M.E.Nontrivial := by
      rw [Set.nontrivial_iff_exists_ne heM]
      use g
      simp only [hgM, true_and]
      exact hg.2.1
    intro h
    by_contra hc
    rw [← circuit_iff_delete_of_disjoint] at h
    have hPtruecoc₃ : M.Connected := by
      have hPtruecoc₄ : 2 ≤ 3 := by simp
      have hPtruecoc₅ : (2 : ENat) ≤ (3 : ENat) := by
        rw [← ENat.coe_le_coe] at hPtruecoc₄
        exact hPtruecoc₄
      have hPtruecoc₆ : M.TutteConnected 2 := by
        apply TutteConnected.mono at hM
        apply hM at hPtruecoc₅
        exact hPtruecoc₅
      rw [tutteConnected_two_iff] at hPtruecoc₆
      exact hPtruecoc₆
    apply IsConnected.nontrivial_of_loopless at hPtruecoc₂
    simp only [loopless_iff_forall_isCircuit] at hPtruecoc₂
    apply hPtruecoc₂ at h
    rw [← one_lt_encard_iff_nontrivial] at h
    rw [← hQtrue, hQtruesing₈] at h
    tauto
    exact hPtruecoc₃
    simp only [disjoint_insert_right, hPetrue, not_false_eq_true, true_and, disjoint_singleton_right, hPftrue]

  have hPtruecoc : (M ＼ {e,f}).IsCocircuit (P true) := Or.elim hPtruecocorcir hPtruecoc₇ (by simp)

  -- Now (P true) ∪ {e,f} is the triad we are seeking.

  apply IsCocircuit.exists_subset_isCocircuit_of_delete at hPtruecoc
  obtain ⟨C', hC'⟩ := hPtruecoc

  have h₃ : Disjoint (P true) {e,f} := by
    simp only [disjoint_insert_right, disjoint_singleton_right, hPetrue, hPftrue]
    tauto
  have h₄ : ((P true) ∪ {e,f}).encard = 3 := by
    rw [encard_union_eq]
    rw [← hQtrue, hQtruesing₈, encard_insert_of_notMem, encard_singleton]
    rw [← add_assoc, one_add_one_eq_two, two_add_one_eq_three]
    simp only [mem_singleton_iff]
    exact hef
    exact h₃
  have h₅ : C' ⊆ (P true) ∪ {e,f} := hC'.2.2
  have h₆ : C'.encard ≤ 3 := by
    apply encard_mono at h₅
    rw [h₄] at h₅
    exact h₅
  have h₇ : 3 ≤ M✶.girth := by
    have h₈ : M✶.TutteConnected (2 + 1) := by
      simp [tutteConnected_dual_iff]
      rw [two_add_one_eq_three]
      exact hM
    have h₉ : 2 * 2 ≤ M✶.E.encard := by
      rw [dual_ground]
      grw [← hG]
      rw [two_mul, two_add_two_eq_four]
    apply TutteConnected.le_girth at h₈
    apply h₈ at h₉
    tauto
  have h₁₀ : M✶.IsCircuit C' := by
    rw [← IsCocircuit]
    exact hC'.1
  have h₁₁ : 3 ≤ C'.encard := by
    apply IsCircuit.girth_le_card at h₁₀
    grw [h₇]
    exact h₁₀
  have h₁₂ : C'.encard = 3 := by
    apply le_antisymm
    exact h₆
    exact h₁₁
  have h₁₃ : C' = (P true) ∪ {e,f} := by
    by_contra hc
    have h₁₄ : ¬((P true) ∪ {e,f}) ⊆ C' := by
      by_contra hc₂
      apply subset_antisymm at h₅
      apply h₅ at hc₂
      tauto
    have h₁₅ : C' ⊂ (P true) ∪ {e,f} := by
      simp only [ssubset_def, h₅, h₁₄, not_false_eq_true, true_and]
    apply Finite.encard_lt_encard at h₁₅
    rw [h₁₂, h₄] at h₁₅
    tauto
    rw [← encard_ne_top_iff, h₁₂]
    simp only [ne_eq, ENat.ofNat_ne_top, not_false_eq_true]
  use C'
  rw [h₁₃, mem_union, mem_insert_iff, eq_self_iff_true, true_or, or_true, true_and]
  rw [← h₁₃]
  have h₁₆ : M.IsTriad C' := by
    rw [isTriad_iff]
    simp only [hC'.1, true_and]
    exact h₁₂
  simp only [h₁₆, true_and]
  have h₁₇ : C' ∩ T = {e,f} := by
    have h₁₈ : {e,f} ⊆ C' ∩ T := by
      simp only [insert_subset_iff, h₁₃, mem_inter_iff, he, mem_union, mem_insert_iff, true_or, or_true, and_true, singleton_subset_iff, mem_singleton_iff, hf]
    apply subset_antisymm
    rw [h₁₃, hg.2.2.2]
    simp only [union_inter_distrib_right]
    have h₁₉ : (P true) ∩ {e,f,g} = ∅ := by
      rw [inter_insert_of_notMem, inter_insert_of_notMem, inter_singleton_eq_empty]
      have h₂₀ : g ∈ (M ＼ {e,f}).E \ (P true) := by
        rw [Separation.compl_true]
        exact hgtrue
      rw [mem_diff] at h₂₀
      simp only [hgMdef, true_and] at h₂₀
      exact h₂₀
      exact hPftrue
      exact hPetrue
    rw [h₁₉]
    simp only [empty_union, inter_subset_left]
    exact h₁₈
  rw [h₁₇]
  rw [encard_insert_of_notMem, encard_singleton]
  rw [one_add_one_eq_two]
  simp only [mem_singleton_iff, hef, not_false_eq_true]
