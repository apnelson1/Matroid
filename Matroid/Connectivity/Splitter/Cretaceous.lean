import Mathlib.Data.Set.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Combinatorics.Matroid.Minor.Order
import Mathlib.Combinatorics.Matroid.Map
import Matroid.ForMathlib.Set
import Matroid.Connectivity.Separation.Two
import Matroid.Triangle

open Set Matroid Function Separation

-- lemma Equiv.swap_eqOn_compl {α : Type*} [DecidableEq α] (x y : α) :
--     EqOn (Equiv.swap x y) (Equiv.refl α) {x, y}ᶜ :=
--   fun a ha ↦ by grind

-- lemma Equiv.swap_image_eq_self

namespace Matroid

variable {α β : Type*} {e f x y : α} {B C D C' D' I X Y Z s : Set α} {i j k l : Bool} {k : ℕ∞}
    {M : Matroid α} {N : Matroid β} {P : M.Separation}

-- Next lemma belongs in Circuit.lean

lemma Circuit.nonempty_circuit_union_of_independent (hX : M.Indep X)
    (hC : M.IsCircuit C) (hCXP : C ⊆ X ∪ D) : (C ∩ D).Nonempty := by
  have hCX : ¬ (C ⊆ X) := fun hCX ↦ hC.not_indep <| hX.subset hCX
  contrapose! hCX
  rwa [union_comm, ← diff_subset_iff, ← diff_self_inter, hCX, diff_empty] at hCXP

-- Next lemma belongs in IndepAxioms.lean

lemma Indep.exists_isBase_disjoint_of_coindep (hI : M.Indep I) (hX : M.Coindep X)
    (hd : Disjoint I X) : ∃ B, M.IsBase B ∧ I ⊆ B ∧ Disjoint B X := by
  obtain ⟨B, hB, hIB, hBX⟩ := hI.exists_isBase_subset_spanning hX.compl_spanning (by grind)
  exact ⟨B, hB, hIB, by grind⟩

--- Following several lemmas may belong in Minor/Order.

lemma IsMinor.isMinor_of_subsets {N : Matroid α} (hd : Disjoint C D) (hNM : N ≤m M ／ C ＼ D)
    (hC : C' ⊆ C) (hD : D' ⊆ D) : N ≤m M ／ C' ＼ D' := by
  refine IsMinor.trans hNM ?_
  have aux := IsRestriction.isMinor (delete_isRestriction_of_subset (M ／ C) (hD))
  rw [contract_delete_comm M (hd), contract_delete_comm M (by grind only [= disjoint_left,
    = subset_def, #f02a, #f7d4])] at aux
  rw [contract_delete_comm M (hd), contract_delete_comm M (by grind only [= disjoint_left,
    = disjoint_comm, = subset_def, #f7d4, #32d2, #f02a])]
  refine IsMinor.trans aux (contract_isMinor_of_subset (M ＼ D') (hC))

lemma IsMinor.exists_partition_of_disjoint_contract_indep_delete_coindep {N : Matroid α}
    (hNM : N ≤m M) (hX : X ⊆ M.E) (hd : Disjoint X N.E) :
    ∃ C D, M.Indep C ∧ M.Coindep D ∧ Disjoint C D ∧ C ∪ D = X ∧ N ≤m M ／ C ＼ D := by
  obtain ⟨C, D, hCD₁, hCD₂, hCD₃, hCD₄⟩ := IsMinor.exists_contract_indep_delete_coindep (hNM)
  subst hCD₄
  clear hNM
  use C ∩ X, D ∩ X
  simp [hCD₁.subset, hCD₂.subset, Set.disjoint_of_subset _ _ hCD₃,
      ← union_inter_distrib_right, show X ⊆ C ∪ D by grind]
  refine IsMinor.isMinor_of_subsets (hCD₃) (IsMinor.refl) (show C ∩ X ⊆ C by simp)
      (show D ∩ X ⊆ D by simp)

lemma IsMinor.exists_smallside_of_separation {N : Matroid α} (hNM : N ≤m M)
    (hN : N.TutteConnected (k + 2)) (hP : P.eConn = k) : ∃ i, (P i ∩ N.E).encard ≤ k := by
  by_contra! hc₁
  have htop : k ≠ ⊤ := by
    by_contra! hc₂
    rw [hc₂] at hc₁
    simp [not_top_lt] at hc₁
  rw [show k+2 = k+1+1 by grind, tutteConnected_iff_forall] at hN
  specialize hN (P := P.induce N)
  refine hN (?_) (?_)
  · grw [eConn_induce_le_of_isMinor P hNM, hP]
  · rw [isTutteSeparation_iff_lt_encard]
    · intro i
      rw [induce_apply_subset _ hNM.subset]
      specialize hc₁ (i := i)
      grw [eConn_induce_le_of_isMinor P hNM]
      grind
    · rw [← lt_top_iff_ne_top]
      grw [eConn_induce_le_of_isMinor P hNM, hP]
      rwa [lt_top_iff_ne_top]

lemma IsMinor.delete_subset_separator (hP : P.eConn = 0) (hX : X ⊆ P i) :
    (M ＼ (P i \ X)) ／ X = M ＼ (P i) := by
  have h₁ : X ⊆ (M ＼ (P i \ X)).E := by
    rw [delete_ground, subset_diff, disjoint_comm, disjoint_diff_iff,
    inter_eq_self_of_subset_right]
    · simp only [subset_refl, and_true]
      apply subset_trans hX P.subset_ground
    · exact hX
  have h₂  : (M ＼ (P i \ X)).Skew X ((M ＼ (P i \ X)).E \ X) := by
    rw [skew_delete_iff]
    constructor
    · rw [delete_ground, diff_diff, diff_union_self, union_eq_self_of_subset_right hX,
        Separation.compl_eq]
      rw [eConn_eq_zero_iff_skew (i := i)] at hP
      refine Skew.mono_left (hP) (hX)
    · constructor
      · rwa [disjoint_comm, disjoint_diff_iff, inter_eq_self_of_subset_right]
      · rw [disjoint_diff_iff, delete_ground, inter_diff_distrib_right, inter_self,
          inter_diff_assoc, diff_self, inter_empty]
        simp
  rw [← contract_eq_delete_iff_skew_compl h₁] at h₂
  rw [h₂, delete_delete, diff_union_self, union_eq_self_of_subset_right]
  exact hX

lemma IsMinor.isMinor_delete_smallside_of_eConn_eq_zero {N : Matroid α} (hNM : N ≤m M)
    (hP : P.eConn = 0) (hPi : Disjoint (P i) N.E) : N ≤m M ＼ P i := by
  refine hNM.isMinor_of_eConn_eq_zero (X := P (!i)) (delete_isMinor ..) ?_ (by simp) (by simpa)
  rwa [← disjoint_iff_subset_not hNM.subset, disjoint_comm]

lemma IsMinor.isMinor_contract_smallside_of_eConn_eq_zero {N : Matroid α} (hNM : N ≤m M)
    (hP : P.eConn = 0) (hPi : Disjoint (P i) N.E) : N ≤m M ／ P i := by
  have aux := hNM.dual.isMinor_delete_smallside_of_eConn_eq_zero (P := P.induce M✶) (i := i)
    (by simpa) (by simpa)
  simpa using aux.dual

lemma IsMinor.isMinor_deleteElem_smallside_of_eConn_eq_zero {N : Matroid α} (hNM : N ≤m M)
    (hP : P.eConn = 0) (hPi : Disjoint (P i) N.E) (he : e ∈ P i) : N ≤m M ＼ {e}  := by
  have h₁ : N ≤m M ＼ P i := isMinor_delete_smallside_of_eConn_eq_zero hNM hP hPi
  have h₂ : M ＼ P i ≤m M ＼ {e} := by
    refine IsMinor.delete_isMinor_delete_of_subset (by simp [IsMinor.refl]) ?_ (by simp)
    rwa [singleton_subset_iff]
  refine IsMinor.trans h₁ h₂

lemma IsMinor.isMinor_contractElem_smallside_of_eConn_eq_zero {N : Matroid α} (hNM : N ≤m M)
    (hP : P.eConn = 0) (hPi : Disjoint (P i) N.E) (he : e ∈ P i) : N ≤m M ／ {e}  := by
  have aux := hNM.dual.isMinor_deleteElem_smallside_of_eConn_eq_zero (P := P.induce M✶) (i := i)
      (by simpa) (by simpa) (by simpa)
  rwa [← dual_contract, dual_isMinor_iff] at aux

-- Splitter Theorem lemmas start at this point

/-
Let `N` be a `3`-connected minor of `M` and `P` be a `(1 + 1)`-separation of `M`,
where `(N.E \ P i).Subsingleton`. (i.e. `N` is mostly contained in `P i`).
Say `P i \ N.E = {e}`.
Then there is a minor `N'` with ground set `insert e (P i)` such that `N ≤m N' ≤m M`.
This should be useful, and can be found with the lemma
`IsMinor.exists_isMinor_of_subset_subset`.
-/
-- = mapEquiv (M ／ X ＼ ((P i) \ (insert x X))) (Equiv.swap x y) := by

lemma Separation.contract_exists_disjoint_base_of_eConn_eq_one {N : Matroid α}
    (hNM : N ≤m M) (hN : Loopless N✶) (hPi : (N.E ∩ (P !i)).Subsingleton) :
    ∃ X, (M ／ (P i)).IsBase X ∧ Disjoint X N.E := by
  -- showing that there exists a disjoint base amounts to showing coindependence.
  -- Possibly this is how the lemma should be stated.
  suffices aux : (M ／ (P i)).Coindep (N.E ∩ P (!i)) by
    obtain ⟨B, hB, hBss⟩ := aux.exists_isBase_subset_compl
    exact ⟨B, hB, by grind⟩
  -- a subsingleton set is either empty or a singleton; the empty case is easy.
  obtain h0 | ⟨e, he⟩ := hPi.eq_empty_or_singleton
  · simp [h0]
  -- otherwise, coindependence of the singleton in `M ／ (P i)` is equivalent to being
  -- a noncoloop in `M` and disjoint from `P i`. We get the disjointness for free.
  rw [coindep_contract_iff, and_iff_left (by grind), he, Coindep, indep_singleton]
  -- `e` is a non-coloop of `N`, and therefore a non-coloop of the major `M`.
  have hNe := hN.isNonloop_of_mem <| show e ∈ N.E by grind [he.symm.subset]
  simpa [he] using hNe.of_isMinor hNM.dual

lemma Separation.isCircuit_union_inter_of_eConn_le_one_bool {C : Bool → Set α}
    (hC : ∀ j, M.IsCircuit (C j)) (hP : P.eConn ≤ 1) (hCP : ∀ i j, (C i ∩ P j).Nonempty) :
    ∀ i j k, M.IsCircuit ((C j ∩ P i) ∪ (C k ∩ P !i)) := by
  intro i j k
  by_cases! aux₁ : j = k
  · rw [← aux₁]
    have h : (C j ∩ P i ∪ C j ∩ P !i) = C j := by
      rw [← inter_union_distrib_left, Separation.union_bool_eq, inter_eq_self_of_subset_left]
      exact (hC j).subset_ground
    rw [h]
    exact hC j
  · rw [← Bool.not_eq] at aux₁
    rw [← aux₁]
    by_cases! aux₂ : j = i
    · rw [aux₂, inter_comm, inter_comm (C !i)]
      have hwin₁ := P.isCircuit_iUnion_inter_of_eConn_le_one (hC) (hP) (hCP)
      rwa [Set.iUnion_bool' _ i] at hwin₁
    · rw [← Bool.not_eq, Bool.not_eq_eq_eq_not] at aux₂
      rw [aux₂, Bool.not_not]
      nth_rw 2 [← Bool.not_not i]
      rw [← Separation.symm_apply, ← Separation.symm_apply P, union_comm,
        inter_comm, inter_comm (C !i)]
      have hCP₂ : ∀ (i j : Bool), (C i ∩ P.symm j).Nonempty := by
        intro i j
        rw [Separation.symm_apply P j]
        exact hCP i !j
      have hwin₂ := P.symm.isCircuit_iUnion_inter_of_eConn_le_one (hC) (by simpa) (hCP₂)
      rwa [Set.iUnion_bool' _ i] at hwin₂

lemma Separation.unique_circuit_of_eConn_le_one {C : Bool → Set α}
    (hC : ∀ j, (M ↾ (X ∪ (P i))).IsCircuit (C j)) (hX : (M ↾ (P !i)).Indep X)
    (hP : P.eConn ≤ 1) (he : ∀ j, (C j ∩ X).Nonempty) : ((C true) ∩ X) = ((C false) ∩ X) := by
  rw [restrict_indep_iff] at hX
  have hCX : ∀ j, (C j) ∩ (P !i) = (C j) ∩ X := by grind only [!Separation.disjoint_bool,
    = subset_def, = disjoint_left, → IsCircuit.subset_ground, = restrict_ground_eq, = mem_inter_iff,
    = mem_union, #3682, #7d79, #36d6, #5a77, #5fc7, #0014]
  have hC₁ : ∀ j, M.IsCircuit (C j) ∧ (C j) ⊆ X ∪ (P i) := by
    intro j
    rw [← restrict_isCircuit_iff]
    exact hC j
  clear hC
  revert hC₁
  intro hC
  have hC₁ : ∀ j, M.IsCircuit (C j) := by
    intro j
    exact (hC j).1
  have heCP : ∀ j k, ((C j) ∩ (P k)).Nonempty := by
    intro j k
    by_cases! aux : k = i
    · subst aux
      refine Circuit.nonempty_circuit_union_of_independent (hX.1) (hC₁ j) ((hC j).2)
    · rw [← Bool.not_eq, Bool.not_eq_eq_eq_not] at aux
      rw [aux, hCX j]
      exact he j
  clear he
  have hC₂ : ∀ j k, M.IsCircuit (((C j) ∩ X) ∪ ((C k) ∩ (P i))) := by
    intro j k
    rw [← hCX j]
    have aux := Separation.isCircuit_union_inter_of_eConn_le_one_bool
        hC₁ hP heCP (!i) (j) (k)
    rwa [Bool.not_not] at aux
  clear hCX hC₁
  by_contra! hcon
  have hx : ∃ x, x ∈ (C true ∩ X) \ (C false ∩ X) := by
    rw [← nonempty_def, diff_nonempty, subset_iff_ssubset_or_eq, not_or]
    constructor
    · have : ¬((C true) ∩ X) ⊂ ((C false) ∩ X) := by
        have := IsCircuit.not_ssubset (hC₂ false true) (hC₂ true true)
        grind only [→ Indep.subset_ground, = ssubset_def, = subset_def, → IsCircuit.subset_ground,
          = mem_inter_iff, = mem_union, #4000, #139e, #54cb, #4989, #2bd4, #8aa3, #6f4a, #022d,
          #06a3]
      grind only [#53bc]
    · exact hcon
  clear hcon
  obtain ⟨x, hx₁⟩ := hx
  obtain ⟨y, hy₁, hy₂⟩ := heCP true i
  obtain ⟨D₁, hD₁, hD₂, hD₃⟩ := IsCircuit.strong_elimination
      ((hC true).1) (hC₂ false true) (hy₁) (by grind only [= mem_union, = mem_inter_iff])
      (by grind only [= mem_diff, = mem_inter_iff])
      (show x ∉ (C false ∩ X) ∪ (C true ∩ (P i)) by grind only [= subset_def,
        !Separation.disjoint_bool, = mem_union, = mem_diff, = mem_inter_iff, = disjoint_left, #36d6,
        #def2])
  have hD₄ : ∀ j, (D₁ ∩ (P j)).Nonempty := by
    intro j
    by_cases! aux : j = i
    · rw [aux]
      refine Circuit.nonempty_circuit_union_of_independent (hX.1) (hD₂)
          (show D₁ ⊆ X ∪ P i by grind only [= subset_def, = mem_union, = mem_diff, = mem_inter_iff])
    · rw [← Bool.not_eq, Bool.not_eq_eq_eq_not] at aux
      simp_rw [aux, nonempty_def, mem_inter_iff]
      use x
      constructor
      · exact hD₃
      · rw [mem_diff, mem_inter_iff] at hx₁
        refine mem_of_subset_of_mem (hX.2) hx₁.1.2
  clear hx₁ hD₃
  have hD₃ := Separation.isCircuit_union_inter_of_eConn_le_one ((hC true).1) (hD₂) (hP)
      (heCP true) (hD₄) (!i)
  rw [Bool.not_not] at hD₃
  have hcon : ((C true ∩ P !i) ∪ D₁ ∩ P i) ⊂ C true := by grind only [= subset_def,
    !Separation.disjoint_bool, = ssubset_def, → IsCircuit.subset_ground, = disjoint_left,
    = mem_union, = mem_inter_iff, = mem_diff, = mem_singleton_iff]
  have := IsCircuit.not_ssubset ((hC true).1) (hD₃)
  contradiction

lemma Separation.exists_subsingleton_independent_in_contraction_of_eConn_one
    (hX : (M ↾ (P !i)).Indep X) (hP : P.eConn ≤ 1) :
    ∃ s : Set α, s.Subsingleton ∧ (M ／ (P i)).Indep (X \ s) := by
  rw [restrict_indep_iff] at hX
  by_cases hcases : (M ／ (P i)).Indep X
  · use ∅
    simpa [subsingleton_empty]
  · rw [← Indep.skew_iff_contract_indep (hX.1) (by simp only [Separation.subset_ground]),
      skew_iff_forall_isCircuit (by grind only [= subset_def, !Separation.disjoint_bool,
        = disjoint_left, = disjoint_comm, #36d6, #def2])] at hcases
    push Not at hcases
    obtain ⟨Y, hY₁, hY₂, _, hY₃⟩ := hcases
    have hy : ∃ y, y ∈ X ∩ Y := by
      rw [not_subset] at hY₃
      obtain ⟨a, ha⟩ := hY₃
      use a
      grind only [= subset_def, = mem_inter_iff, = mem_union, #f1e5]
    obtain ⟨y, hy⟩ := hy
    use {y}
    simp [subsingleton_singleton]
    by_contra hc
    rw [← Indep.skew_iff_contract_indep (by simp [(hX.1).subset])
        (by simp only [Separation.subset_ground]),
        skew_iff_forall_isCircuit
        (by grind only [= subset_def, !Separation.disjoint_bool, = disjoint_left, = disjoint_comm,
        = mem_diff, #36d6, #def2])
        (by grind only [→ Indep.subset_ground, = subset_def, = mem_diff, #139e])] at hc
    push Not at hc
    obtain ⟨Z, hZ₁, hZ₂, _, hZ₃⟩ := hc
    let C := fun j ↦ bif j then Y else Z
    have hC : ∀ j, (M ↾ (X ∪ (P i))).IsCircuit (C j) := by
      intro j
      rw [restrict_isCircuit_iff]
      by_cases hj : j
      · simp [hj, C]
        exact And.intro hY₁ hY₂
      · rw [Bool.not_eq_true] at hj
        simp [hj, C]
        grind only [= subset_def, = mem_union, = mem_diff, #9295]
    have he : ∀ j, (C j ∩ X).Nonempty := by
      intro j
      by_cases hec : j
      · simp [hec, C, nonempty_def]
        rw [not_subset] at hY₃
        grind only [= subset_def, = mem_inter_iff, #26bf]
      · rw [Bool.not_eq_true] at hec
        simp [hec, C, nonempty_def]
        rw [not_subset] at hZ₃
        grind only [= subset_def, = mem_union, = mem_diff, #d7c4, #3379, #9295]
    rw [← restrict_indep_iff] at hX
    have aux₁ := Separation.unique_circuit_of_eConn_le_one (hC) (hX) (hP) (he)
    simp [C, Set.ext_iff] at aux₁
    specialize aux₁ (x := y)
    rw [mem_inter_iff] at hy
    grind only [→ Indep.subset_ground, !Separation.disjoint_bool, = subset_def, = disjoint_left,
      = mem_union, = mem_diff, = mem_singleton_iff, #9295, #b487, #def2]

lemma Separation.coindependent_inter_contraction_coloopless_minor {N : Matroid α}
    (hN : Coloopless N) (hNM : N ≤m M) (hPi : (N.E ∩ (P !i)).Subsingleton) :
    (M ／ P i).Coindep (N.E ∩ (P !i)) := by
  by_contra hc₁
  rw [not_coindep_iff] at hc₁
  by_cases he : (N.E ∩ P !i).Nonempty
  · have aux := And.intro he hPi
    rw [← Set.exists_eq_singleton_iff_nonempty_subsingleton] at aux
    obtain ⟨a, ha⟩ := aux
    rw [ha, codep_iff, coindep_contract_iff, not_and_or] at hc₁
    simp at hc₁
    rcases hc₁.1 with ⟨ha₁⟩
    · have ha₂ : a ∈ M.E ∩ N.E := by
        constructor
        · refine mem_of_subset_of_mem (P.subset' (!i)) hc₁.2
        · rw [← singleton_subset_iff, ← ha, subset_def, inter_def]
          grind => instantiate only [usr mem_setOf_eq]
      rw [not_isNonColoop_iff] at ha₁
      have aux := ha₁.of_isMinor (show a ∈ N.E by simp [ha₂.2]) hNM
      rw [← dual_isLoop_iff_isColoop] at aux
      rw [coloopless_iff, loopless_iff_forall_not_isLoop] at hN
      grind only [= mem_inter_iff, #4c6f]
    · grind only [!Separation.disjoint_bool, = disjoint_left, #def2]
  · rw [not_nonempty_iff_eq_empty] at he
    rw [he, codep_def, ← not_indep_iff] at hc₁
    simp [empty_indep] at hc₁

lemma Separation.exists_basis_contraction_coloopless_minor {N : Matroid α} (hP : P.eConn ≤ 1)
    (hNc : (M ／ P i).Coindep (N.E ∩ (P !i))) (hC : (M ＼ (N.E ∪ P i)).Indep C) :
    ∃ B, (M ／ P i).IsBase B ∧ (C \ B).Subsingleton ∧ B ∩ N.E = ∅ := by
  have hC₁ : (M ↾ (P !i)).Indep C := by simp_all [delete_indep_iff]
  have aux := Separation.exists_subsingleton_independent_in_contraction_of_eConn_one (hC₁) (hP)
  obtain ⟨s, hs₁, hs₂⟩ := aux
  have hd : Disjoint (C \ s) (N.E ∩ (P !i)) := by
    grind only [→ Indep.subset_ground, = disjoint_left, = disjoint_comm, = delete_ground,
    = subset_def, = mem_inter_iff, = mem_diff, = mem_union, #801a]
  have aux := Indep.exists_isBase_disjoint_of_coindep (hs₂) (hNc) (hd)
  obtain ⟨B, hB₁, hB₂, hB₃⟩ := aux
  clear hs₂ hC₁ hd
  use B
  simp [hB₁]
  constructor
  · have aux₁ : C \ B ⊆ s := by grind only [= subset_def, = mem_diff, #a11b]
    have aux₂ := Subsingleton.eq_or_eq_of_subset (hs₁) (aux₁)
    rcases aux₂ with aux₃ | aux₄
    · simp [aux₃, subsingleton_empty]
    · simpa [aux₄]
  · grind only [= disjoint_left, → IsBase.subset_ground, = contract_ground, = subset_def,
    = Separation.compl_eq, = mem_inter_iff, = mem_empty_iff_false, #bc5b, #d9f8, #ee00]

lemma Separation.forall_circuits_meeting_basis_largeside {N : Matroid α} (hP : P.eConn ≤ 1)
    (hPi : (N.E ∩ (P !i)).Subsingleton) (hC : M.Indep C) (hD : M.Coindep D) (hCD : Disjoint C D)
    (hCDP : C ∪ D  = (P !i) \ N.E) (hNM : N ≤m M ／ C ＼ D) (hB : (M ／ P i).IsBase B)
    (hBC : (C \ B).Subsingleton) (hBN : B ∩ N.E = ∅) :
    ∀ C₀, (M ＼ (D \ B)).IsCircuit C₀ → ¬C₀ ⊆ P i ∪ N.E ∪ C → C₀ ⊆ B ∪ C := by
  intro C₀ hC₀ hCPiN
  sorry

lemma IsMinor.contract_disjoint_base_of_eConn_eq_one {N : Matroid α} (hP : P.eConn ≤ 1)
    (hN : Coloopless N) (hNM : N ≤m M) (hPi: (N.E ∩ (P !i)).Subsingleton) :
    ∃ X, (M ／ (P i)).IsBase X ∧ N ≤m (M ／ X) := by
  have hPM : (P !i) \ N.E ⊆ M.E := by
    simp only [diff_subset_iff]
    refine subset_union_of_subset_right (P.subset' (!i)) N.E
  have aux := IsMinor.exists_partition_of_disjoint_contract_indep_delete_coindep (hNM)
      (hPM) (by grind only [= disjoint_left, = mem_diff])
  obtain ⟨C, D, hC, hD, hCD, hCDP, hNM₀⟩ := aux
  have hNc := Separation.coindependent_inter_contraction_coloopless_minor (hN) (hNM) (hPi)
  have hC₀ : (M ＼ (N.E ∪ P i)).Indep C := by
    simp [delete_indep_iff, hC]
    constructor
    · grind only [→ subset, = disjoint_left, = disjoint_comm, = subset_def, = delete_ground,
      = contract_ground, = mem_diff, #dab3]
    . grind only [!Separation.disjoint_bool, → Indep.subset_ground, = disjoint_left,
      = disjoint_comm, = subset_def, = mem_union, = mem_diff, #f02a, #7ef2, #def2, #7691]
  clear hPM
  obtain ⟨B, hB₁, hB₂, hB₃⟩ := Separation.exists_basis_contraction_coloopless_minor (hP) (hNc) (hC₀)
  use B
  simp [hB₁]
  suffices hskew : (M ／ C ＼ (D \ B)).Skew (B \ C) (P i ∪ N.E)
  · refine IsMinor.trans (hNM₀) (?_)
    have hskew₁ : (B \ C) ⊆ D := by
      have aux := hB₁.subset_ground
      rw [contract_ground, P.compl_eq] at aux
      rw [diff_subset_iff, hCDP, subset_diff, disjoint_iff_inter_eq_empty]
      exact And.intro aux hB₃
    have hskew₂ : (D \ B) ∪ (B \ C) = D := by grind only [= disjoint_comm, = subset_def,
      = disjoint_left, = mem_union, = mem_diff, #09e7, #e397, #6798, #0772]
    have hskew₃ : P i ∪ N.E = (M ／ C ＼ (D \ B)).E \ (B \ C) := by
      rw [delete_ground, contract_ground, diff_diff, hskew₂, diff_diff, hCDP,
          diff_diff_eq_sdiff_union]
      · rw [Separation.compl_eq, Bool.not_not]
      · have aux := hNM₀.subset
        rw [delete_ground, contract_ground, diff_diff, subset_diff] at aux
        exact aux.1
    rw [hskew₃] at hskew
    clear hskew₃
    have hskew₃ : (B \ C) ⊆ (M ／ C ＼ (D \ B)).E := by
      grind only [→ Indep.subset_ground, = delete_ground, = subset_def, = contract_ground,
          = mem_diff, #e397, #c367]
    have hskew₄ : (M ／ C ＼ (D \ B)) ／ (B \ C) = (M ／ C ＼ (D \ B)) ＼ (B \ C) := by
      rwa [← contract_eq_delete_iff_skew_compl] at hskew
    rw [delete_delete, hskew₂] at hskew₄
    rw [← hskew₄, contract_delete_comm M (by grind only [= disjoint_left, = mem_diff, #f02a]),
        contract_contract]
    clear hskew₁ hskew₂ hskew₃ hskew₄
    have hskew₂ : M ＼ (D \ B) ／ (C ∪ B \ C) ≤m M ／ (C ∪ B \ C) := by
      have aux₁ : Disjoint (C ∪ B \ C) (D \ B) := by grind only [= disjoint_left, = disjoint_comm,
        = mem_union, = mem_diff, #f02a]
      rw [← contract_delete_comm M (aux₁)]
      have aux₂ := IsMinor.isMinor_of_subsets (aux₁) (refl (M := M ／ (C ∪ B \ C) ＼ (D \ B)))
          (subset_refl (C ∪ B \ C)) (empty_subset (D \ B))
      rwa [delete_empty] at aux₂
    have hskew₃ : M ／ (C ∪ B \ C) ≤m M ／ B := by
      rw [union_diff_self]
      refine contract_isMinor_of_subset (M) (by simp only [subset_union_right])
    refine IsMinor.trans (hskew₂) (hskew₃)
  · have hdCDB := disjoint_of_subset (subset_refl C) (show D \ B ⊆ D by simp only [diff_subset_iff,
        subset_union_right]) (hCD)
    have hdBCPiN : Disjoint (B \ C) (P i ∪ N.E) := by
      have aux := hB₁.subset_ground
      rw [contract_ground, subset_diff, disjoint_iff_inter_eq_empty] at aux
      simp [disjoint_union_right, disjoint_diff_iff, aux.2, hB₃]
    have hBC : B \ C ⊆ ((M ／ C ＼ (D \ B))).E := by
      rw [diff_subset_iff, contract_delete_comm, contract_ground, union_diff_cancel,
          delete_ground, diff_diff_eq_sdiff_union]
      · simp [subset_union_right]
      · have aux₂ := hB₁.subset_ground
        rw [contract_ground, subset_diff] at aux₂
        exact aux₂.1
      · simp [delete_ground, subset_diff, hC.subset_ground]
        exact hdCDB
      · exact hdCDB
    have hPiN : (P i ∪ N.E) ⊆ ((M ／ C ＼ (D \ B))).E := by
      have aux₁ : (P i ∪ N.E) ⊆ M.E \ (C ∪ D) := by
        rw [hCDP, diff_diff_eq_sdiff_union]
        · rw [P.compl_eq, Bool.not_not]
        · exact hNM.subset
      grind only [= delete_ground, = subset_def, = contract_ground, = mem_diff, = mem_union, #bd78]
    rw [skew_iff_forall_isCircuit (hdBCPiN) (hBC) (hPiN)]
    clear hdBCPiN hBC hPiN
    by_contra! hc
    obtain ⟨C₀, hC₁, hC₂, hC₃, hC₄⟩ := hc
    rw [contract_delete_comm] at hC₁
    · obtain ⟨C₁, hC₅, hC₆, hC₇⟩ := IsCircuit.exists_subset_isCircuit_of_contract (hC₁)
      have aux := Separation.forall_circuits_meeting_basis_largeside (hP) (hPi) (hC) (hD) (hCD)
          (hCDP) (hNM₀) (hB₁) (hB₂) (hB₃) C₁ hC₅
          (show ¬C₁ ⊆ P i ∪ N.E ∪ C by grind only [→ IsCircuit.subset_ground,
            = subset_def, = contract_ground, = mem_union, = mem_diff, #f739, #46a2, #14d2])
      grind only [→ Indep.subset_ground, = subset_def, = delete_ground, = mem_diff, = mem_union,
        #f739, #cc79, #138f, #801a]
    · exact hdCDB

lemma splitter_no_triangle (hM : M.TutteConnected 3) (hN : N.TutteConnected 3) (fNM : N <i M)
    (hTriad : ∀ e T, M.IsDeletable N e → M.IsTriad T → e ∉ T)
    (hTriangle : ∀ e T, M.IsContractible N e → M.IsTriangle T → e ∉ T) :
    ∃ e, (M.IsDeletable N e ∧ (M ＼ {e}).TutteConnected 3)
    ∨ (M.IsContractible N e ∧ (M ／ {e}).TutteConnected 3) := by
  rw [show (3 : ℕ∞) = 2 + 1 from rfl] at *
  obtain ⟨e, he⟩ := StrictIsoMinor.exists_isDeletable_or_isContractible (fNM)
  clear fNM
  wlog hed : M.IsDeletable N e generalizing M N with aux
  · rw [or_iff_left hed, ← dual_isDeletable_dual_iff] at he
    specialize aux hM.dual hN.dual (by simpa) (by simpa) (Or.inr he) he
    obtain ⟨f, hf⟩ := aux
    use f
    rwa [dual_isContractible_dual_iff, dual_isDeletable_dual_iff, ← dual_contract, ← dual_delete,
      tutteConnected_dual_iff, tutteConnected_dual_iff, or_comm] at hf
  clear he
  by_contra! hcon
  have henot3con : ¬ (M ＼ {e}).TutteConnected (2 + 1) := (hcon e).1 hed
  rw [not_tutteConnected_iff_exists] at henot3con
  obtain ⟨P, hP⟩ := henot3con

  /-
  We are under the hypotheses that if M/e has an N-minor, then e is not in a triangle, and
  if M\e has an N-minor, then e is not in a triad. The other case leads to 4-element fans.

  At this point we have used duality to assume that there is an element e such that
  M\e has an N-minor. Note that e is not in a triad. If M\e is 3-connected, then we are done,
  so we assume that M\e has a 2-separation P.

  We show that P has a "small side" relative to a copy of N, that is, for a fixed copy
  of N, there is a side of P that contains at most one element of that copy. This small
  side cannot have rank 1, because M is simple. It cannot have corank 1, because then e
  would be in a triad, and e is a deletable element. So by a lemma, the small side contains
  a "flexible" element, f, meaning that both M \ f and M / f have isomorphic copies of N.
  The hypotheses imply f is in no triangle and in no triad, so that si(M/f) = M/f and
  co(M\f) = M\f. Now we can apply Bixby to f and deduce that the splitter theorem holds.
  -/

  sorry
