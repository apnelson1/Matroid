import Mathlib.Data.Set.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Combinatorics.Matroid.Minor.Order
import Mathlib.Combinatorics.Matroid.Map
import Mathlib.Tactic.IntervalCases
import Matroid.ForMathlib.Set
import Matroid.Connectivity.Separation.Two
import Matroid.Triangle

open Set Matroid Function Separation

-- lemma Equiv.swap_eqOn_compl {α : Type*} [DecidableEq α] (x y : α) :
--     EqOn (Equiv.swap x y) (Equiv.refl α) {x, y}ᶜ :=
--   fun a ha ↦ by grind

-- lemma Equiv.swap_image_eq_self

namespace Matroid

variable {α β : Type*} {e f x y : α} {B C D C' D' I X Y Z s : Set α} {b i j k l : Bool} {k : ℕ∞}
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

-- this doesn't need to be a lemma imo.
lemma IsMinor.isMinor_of_subsets {N : Matroid α} (hd : Disjoint C D) (hNM : N ≤m M ／ C ＼ D)
    (hC : C' ⊆ C) (hD : D' ⊆ D) : N ≤m M ／ C' ＼ D' :=
  hNM.trans <| contract_delete_isMinor_contract_delete _ hd hC hD

lemma IsMinor.exists_partition_of_disjoint_contract_indep_delete_coindep {N : Matroid α}
    (hNM : N ≤m M) (hX : X ⊆ M.E) (hd : Disjoint X N.E) :
    ∃ C D, M.Indep C ∧ M.Coindep D ∧ Disjoint C D ∧ C ∪ D = X ∧ N ≤m M ／ C ＼ D := by
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := IsMinor.exists_contract_indep_delete_coindep (hNM)
  exact ⟨C ∩ X, D ∩ X, hC.inter_right _, hD.inter_right _, by grind, by grind,
    contract_delete_isMinor_contract_delete _ hCD inter_subset_left inter_subset_left⟩

lemma IsMinor.exists_smallside_of_separation {N : Matroid α} {k : ENat} (hNM : N ≤m M)
    (hN : N.TutteConnected (k + 1 + 1)) (hP : P.eConn ≤ k) : ∃ i, (P i ∩ N.E).encard ≤ k := by
  have hns := hN.not_isTutteSeparation (P := P.induce N)
    (by grw [P.eConn_induce_le_of_isMinor hNM, hP])
  contrapose! hns
  refine isTutteSeparation_of_lt_encard fun i ↦ ?_
  grw [eConn_induce_le_of_isMinor _ hNM, hP, induce_apply_subset _ hNM.subset]
  exact hns i

lemma delete_contract_eq_delete_of_subset (hP : P.eConn = 0) (hX : X ⊆ P i) :
    (M ＼ (P i \ X)) ／ X = M ＼ (P i) := by
  rw [eConn_eq_zero_iff_skew (i := i)] at hP
  rw [delete_eq_restrict, delete_eq_restrict, restrict_contract_eq_contract_restrict,
    diff_diff, diff_union_of_subset hX, P.compl_eq, (hP.mono_left hX).contract_restrict_eq]
  grw [diff_diff_right, ← subset_union_right,
    inter_eq_self_of_subset_right (hX.trans P.subset_ground)]

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
  obtain rfl | rfl := j.eq_or_eq_not k
  · specialize hC j
    rwa [← inter_union_distrib_left, P.union_bool_eq, inter_eq_self_of_subset_left hC.subset_ground]
  exact P.isCircuit_union_inter_of_eConn_le_one (hC !k) (hC k) hP (fun i ↦ hCP ..)
    (fun i ↦ hCP ..) i

lemma Separation.unique_circuit_of_eConn_le_one {C : Bool → Set α}
    (hC : ∀ j, (M ↾ (X ∪ (P i))).IsCircuit (C j)) (hX : (M ↾ (P !i)).Indep X)
    (hP : P.eConn ≤ 1) (he : ∀ j, (C j ∩ X).Nonempty) : ((C true) ∩ X) = ((C false) ∩ X) := by
  have hi : (M ↾ (X ∪ P i)).Indep X := by
    rw [restrict_indep_iff, and_iff_left subset_union_left]
    exact hX.of_restrict
  have hconn : (M ↾ (X ∪ P i)).eConn X ≤ 1 := by
    grw [← eConn_compl, restrict_ground_eq, union_diff_cancel_left, eConn_restrict_le,
      P.eConn_eq, hP]
    grw [hX.subset_ground, restrict_ground_eq, (P.disjoint_bool _).symm.inter_eq]
  obtain ⟨J, hJX, hJ⟩ := hi.exists_forall_inter_circuit_eq hconn
  rw [hJ _ (hC _) (he _), hJ _ (hC _) (he _)]

lemma Separation.exists_subsingleton_independent_in_contraction_of_eConn_one
    (hX : (M ↾ (P !i)).Indep X) (hP : P.eConn ≤ 1) :
    ∃ s : Set α, s.Subsingleton ∧ (M ／ (P i)).Indep (X \ s) := by
  have hn : (M ／ P i).nullity X ≤ 1 := by
    grw [← nullity_project_eq_nullity_contract, project_nullity_eq_nullity_add_eLocalConn,
      hX.of_restrict.nullity_eq, zero_add, M.eLocalConn_mono_left hX.subset_ground,
      restrict_ground_eq, eLocalConn_comm, ← P.eConn_eq_eLocalConn, hP]
  obtain ⟨B, hB⟩ := (M ／ P i).exists_isBasis' X
  refine ⟨X \ B, ?_, ?_⟩
  · rwa [← encard_le_one_iff_subsingleton, ← hB.nullity_eq]
  rw [diff_diff_cancel_left hB.subset]
  exact hB.indep

lemma Separation.coindependent_inter_contraction_coloopless_minor {N : Matroid α}
    (hN : Coloopless N) (hNM : N ≤m M) (hPi : (N.E ∩ (P !i)).Subsingleton) :
    (M ／ P i).Coindep (N.E ∩ (P !i)) := by
  rw [coindep_contract_iff, and_iff_left ((P.disjoint_bool i).symm.mono_left inter_subset_right)]
  exact (hN.subsingleton_coindep hPi).of_isMinor hNM.dual

lemma Separation.indep_coindep_exists_basis_contraction_minor
    (hC : C ⊆ P !i) (hDc : M.Coindep ((P !i) \ C)) :
    ∃ B, (M ／ P i).IsBase B ∧ M ／ C ＼ D ≤m M ／ B := by
  rw [coindep_iff_compl_spanning
    (by grind only [= subset_def, → Indep.subset_ground, = dual_ground]),
    diff_diff_eq_sdiff_union (subset_trans hC P.subset), P.compl_eq, Bool.not_not,
    union_comm] at hDc
  have h₁ : (M ／ (P i)).Spanning C := by
    rw [contract_spanning_iff]
    exact ⟨hDc, by grind only [= subset_def, !Separation.disjoint_bool, = disjoint_left,
      = disjoint_comm, #758b, #def2]⟩
  rw [spanning_iff_exists_isBase_subset] at h₁
  obtain ⟨B, hB, hBC⟩ := h₁
  use B
  refine ⟨hB, ?_⟩
  have h₁ := delete_isMinor_delete_of_subset (M ／ C) (show ∅ ⊆ D by simp only [empty_subset])
  rw [delete_empty] at h₁
  exact IsMinor.trans h₁ (contract_isMinor_of_subset (M) (hBC))

/-
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
      grind only [→ Indep.subset_ground, = delete_ground, = subset_def, = dual_ground,
        = contract_ground, = mem_diff, #e397, #c367]
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
-/

lemma circuit_of_element_contraction (hC : (M ／ {e}).IsCircuit C) :
    M.IsCircuit C ∨ M.IsCircuit (C ∪ {e}) := by
  have h₁ := IsCircuit.exists_subset_isCircuit_of_contract hC
  obtain ⟨C₁, hC₁, hC₂, hC₃⟩ := h₁
  by_cases! h₂ : C₁ = C
  · apply Or.inl
    rwa [h₂] at hC₁
  · apply Or.inr
    have h₃ : C ∪ {e} ⊆ C₁ := by
      grind only [= subset_def, = mem_union, = mem_singleton_iff, #2a2c, #4326, #8c6e, #2acb]
    have h₄ := subset_antisymm hC₃ h₃
    rwa [h₄] at hC₁

lemma exists_circuit_contract_elem_girth_decrease (k : ENat) (hk : k ≠ ⊤) (hg₁ : k ≤ M.girth)
    (hg₂ : (M ／ {e}).girth < k) : ∃ C, M.IsCircuit C ∧ C.encard = k ∧ e ∈ C := by
  by_cases! he : e ∈ M.E
  · rw [girth_lt_iff] at hg₂
    obtain ⟨C, hC₁, hC₂⟩ := hg₂
    use C ∪ {e}
    have h₁ := circuit_of_element_contraction hC₁
    have h₂ : M.IsCircuit (C ∪ {e}) := by
      by_contra! hc
      have h₃ := Or.resolve_right h₁ hc
      rw [le_girth_iff] at hg₁
      specialize hg₁ C h₃
      grind only
    constructor
    · exact h₂
    · constructor
      · rw [le_girth_iff] at hg₁
        specialize hg₁ (C ∪ {e}) h₂
        rw [union_singleton, encard_insert_of_notMem (by grind only [→ IsCircuit.subset_ground,
          = contract_ground, = subset_def, = mem_diff, = mem_singleton_iff, #524e])] at hg₁
        rw [union_singleton, encard_insert_of_notMem (by grind only [→ IsCircuit.subset_ground,
          = contract_ground, = subset_def, = mem_diff, = mem_singleton_iff, #524e])]
        enat_to_nat!
        grind only
      · simp only [union_singleton, mem_insert_iff, true_or]
  · have h : Disjoint {e} M.E := by grind only [= disjoint_left, = mem_singleton_iff]
    rw [← contract_eq_self_iff] at h
    rw [h] at hg₂
    grind only

lemma simple_cosimple_of_deletion_no_triangle_splitter  {N : Matroid α} (hs : M.Simple)
    (hcs : M✶.Simple) (hT : ∀ e T, Nonempty (N ≤i (M ＼ {e})) → M.IsTriad T → e ∉ T)
    (heN : N ≤m M ＼ {e}) : (M ＼ {e}).Simple ∧ (M ＼ {e})✶.Simple := by
  have hg : 3 ≤ M✶.girth := by rwa [three_le_girth_iff]
  constructor
  · have h₁ : (M ↾ M.E).Simple := by simp_all only [restrict_ground_eq_self]
    have h₂ := h₁.subset (show (M ＼ {e}).E ⊆ M.E by simp_all only
      [restrict_ground_eq_self, delete_ground, diff_subset_iff,
      singleton_union, subset_insert])
    rwa [delete_ground, restrict_compl] at h₂
  · by_contra! hc
    rw [← three_le_girth_iff] at hc
    push Not at hc
    rw [show (3 : ENat) = 2 + 1 by rfl, ENat.lt_add_one_iff (by simp [ENat.ofNat_ne_top])] at hc
    rw [dual_delete, ← ENat.lt_add_one_iff (by simp [ENat.ofNat_ne_top]),
        show 2 + 1 = (3 : ENat) by rfl] at hc
    have aux := exists_circuit_contract_elem_girth_decrease (k := 3)
        (show (3 : ENat) ≠ ⊤ by simp [ENat.ofNat_ne_top]) hg hc
    obtain ⟨C, hC₁, hC₂, hC₃⟩ := aux
    have hT₁ : M.IsTriad C := by
      constructor
      · exact hC₁
      · exact hC₂
    specialize hT e C ⟨heN.isoMinor⟩ hT₁
    contradiction

#check Separation.isoMinor_contract_of_notMem_closure

lemma splitter_no_triangle_minor {N : Matroid α} (hM : M.TutteConnected (2 + 1)) (hME : 4 ≤ M.E.encard)
    (hN : N.TutteConnected (2 + 1)) (hNM : N <m M)
    (hr : ∀ e b T, Nonempty (N ≤i M.remove b {e}) → (M.bDual !b).IsTriangle T → e ∉ T) :
    ∃ e b, Nonempty (N ≤i M.remove b {e}) ∧ (M.remove b {e}).TutteConnected (2 + 1) := by
  obtain ⟨e, heM, heN⟩ := hNM.exists_isMinor_contractElem_or_deleteElem
  wlog hed : N ≤m M ＼ {e} generalizing M N with aux₁
  · rw [← dual_ground] at heM
    have aux₂ : N✶ ≤m M✶ ＼ {e} := by
       have aux₃ := Or.resolve_right heN hed
       rwa [← dual_delete_dual, ← dual_isMinor_iff, dual_dual] at aux₃
    have aux₄ : ∀ (e : α) (b : Bool) (T : Set α), Nonempty (N✶ ≤i M✶.remove b {e}) →
        (M✶.bDual !b).IsTriangle T → e ∉ T := by sorry
    specialize aux₁ hM.dual (by simp_all only [dual_ground, or_false]) hN.dual hNM.dual aux₄ heM
        (Or.inr aux₂) aux₂
    obtain ⟨e, b, he₁, he₂⟩ := aux₁
    use e
    use !b
    constructor
    · rwa [← nonempty_isoMinor_dual_iff, remove_dual, dual_dual, dual_dual] at he₁
    · rwa [show b = !!b by simp only [Bool.not_not], ← remove_dual, tutteConnected_dual_iff] at he₂
  · clear heN hNM
    by_cases! hc : ¬(M ＼ {e}).TutteConnected (2 + 1)
    · rw [not_tutteConnected_iff_exists] at hc
      obtain ⟨P, hP₁, hP₂⟩ := hc
      -- obtain ⟨j, hi⟩ := IsMinor.exists_smallside_of_separation hed
      sorry
    · use e
      use false
      constructor
      · rw [remove_false]
        exact ⟨hed.isoMinor⟩
      · rwa [remove_false]

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
