import Mathlib.Data.Set.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Combinatorics.Matroid.Minor.Order
import Mathlib.Combinatorics.Matroid.Map
import Matroid.ForMathlib.Set
import Matroid.Triangle

open Set Matroid Function Separation

namespace Matroid

variable {α β : Type*} {e f x y: α} {i j : Bool} {k : ℕ∞} {X Y : Set α}
    {M : Matroid α} {N : Matroid β} {P : M.Separation}

theorem splitter_theorem (hM : M.TutteConnected 3) (hN : N.TutteConnected 3) (fNM : N <i M)
    (hNT : ¬ N.Triadular) : ∃ e, (M.IsDeletable N e ∧ (M ＼ {e}).TutteConnected 3)
    ∨ (M.IsContractible N e ∧ (M ／ {e}).TutteConnected 3) := by
  sorry

lemma IsMinor.exists_smallside_of_separation {N : Matroid α} (hNM : N ≤m M)
    (hN : N.TutteConnected (k + 2)) (hPconn : P.eConn = k) : ∃ i, (P i ∩ N.E).encard ≤ k := by
  by_contra! hc
  have htop : k ≠ ⊤ := by
    by_contra! hcc
    rw [hcc] at hc
    simp [not_top_lt] at hc
  rw [show k+2 = k+1+1 by grind, tutteConnected_iff_forall] at hN
  specialize hN (P:= P.induce hNM.subset)
  refine hN (?_) (?_)
  · grw [eConn_induce_le_of_isMinor P hNM, hPconn]
  · rw [isTutteSeparation_iff_lt_encard]
    · intro i
      rw [induce_apply]
      specialize hc (i:= i)
      grw [eConn_induce_le_of_isMinor P hNM]
      grind
    · rw [← lt_top_iff_ne_top]
      grw [eConn_induce_le_of_isMinor P hNM, hPconn]
      rwa [lt_top_iff_ne_top]

lemma ENat.encard_le_zero_iff_isempty {s : Set α} : s.encard ≤ 0 ↔ s = ∅ := by
  constructor
  · intro h
    have h₁ : s.encard.toNat ≤ 0 := by simp_all
    rw [le_zero_iff] at h₁
    have h₂ : s.encard = 0 := by simp_all
    rwa [encard_eq_zero] at h₂
  · intro h
    rw [← encard_eq_zero] at h
    grind

lemma IsMinor.delete_subset_separator (hPconn : P.eConn = 0) (hX : X ⊆ P i) :
    (M ＼ (P i \ X)) ／ X = M ＼ (P i):= by
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
      rw [eConn_eq_zero_iff_skew (i := i)] at hPconn
      refine Skew.mono_left (hPconn) (hX)
    · constructor
      · rwa [disjoint_comm, disjoint_diff_iff, inter_eq_self_of_subset_right]
      · rw [disjoint_diff_iff, delete_ground, inter_diff_distrib_right, inter_self,
          inter_diff_assoc, diff_self, inter_empty]
        simp
  rw [← contract_eq_delete_iff_skew_compl h₁] at h₂
  rw [h₂, delete_delete, diff_union_self, union_eq_self_of_subset_right]
  exact hX

lemma IsMinor.isMinor_delete_smallside_of_eConn_eq_zero {N : Matroid α} (hNM : N ≤m M)
    (hPconn : P.eConn = 0) (hPi : (P i ∩ N.E).encard ≤ 0) : N ≤m M ＼ P i := by
  rw [ENat.encard_le_zero_iff_isempty] at hPi
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := hNM.exists_eq_contract_delete_disjoint
  rw [delete_ground, contract_ground, diff_diff, ← inter_diff_assoc,
        inter_eq_self_of_subset_left P.subset_ground, diff_eq_empty] at hPi
  have h₁ : M ／ C ＼ D ≤m M ／ (P i ∩ C) ＼ (P i ∩ D) := by
    refine delete_isMinor_delete_of_subset (?_) (by simp) (?_)
    · refine contract_isMinor_contract_of_subset (by simp[IsMinor.refl]) (by simp) (by grind)
    · rw [contract_ground, contract_ground]
      grind
  nth_rw 2 [contract_delete_comm] at h₁
  · have h₂ : P i ∩ D = P i \ (P i ∩ C) := by
      grind
    rwa [h₂, IsMinor.delete_subset_separator (hPconn)] at h₁
    grind
  · grind

lemma IsMinor.isMinor_contract_smallside_of_eConn_eq_zero {N : Matroid α} (hNM : N ≤m M)
    (hPconn : P.eConn = 0) (hPi : (P i ∩ N.E).encard ≤ 0) : N ≤m M ／ P i := by
  have aux := hNM.dual.isMinor_delete_smallside_of_eConn_eq_zero (P := P.dual) (i := i) (by simpa)
    (by grind)
  rwa [← dual_contract, dual_isMinor_iff] at aux

lemma IsMinor.isMinor_deleteElem_smallside_of_eConn_eq_zero {N : Matroid α} (hNM : N ≤m M)
    (hPconn : P.eConn = 0) (hPi : (P i ∩ N.E).encard ≤ 0) (he : e ∈ P i) : N ≤m M ＼ {e}  := by
  have h₁ : N ≤m M ＼ P i := isMinor_delete_smallside_of_eConn_eq_zero hNM hPconn hPi
  have h₂ : M ＼ P i ≤m M ＼ {e} := by
    refine IsMinor.delete_isMinor_delete_of_subset (by simp [IsMinor.refl]) ?_ (by simp)
    rwa [singleton_subset_iff]
  refine IsMinor.trans h₁ h₂

lemma IsMinor.isMinor_contractElem_smallside_of_eConn_eq_zero {N : Matroid α} (hNM : N ≤m M)
    (hPconn : P.eConn = 0) (hPi : (P i ∩ N.E).encard ≤ 0) (he : e ∈ P i) : N ≤m M ／ {e}  := by
  have aux := hNM.dual.isMinor_deleteElem_smallside_of_eConn_eq_zero (P := P.dual) (i := i)
      (by simpa) (by grind) (by simpa)
  rwa [← dual_contract, dual_isMinor_iff] at aux

lemma Separation.disjoint_true_iff_subset_false (hX : X ⊆ M.E) :
    Disjoint X (P i) ↔ X ⊆ (P !i) := by
  constructor
  · intro h
    rw [← P.compl_eq, subset_diff]
    grind
  · intro h
    refine disjoint_of_subset (h) (show (P i) ⊆ (P i) by simp) (?_)
    nth_rw 2 [← Bool.not_not i]
    refine P.disjoint_bool (!i)

lemma Separation.indep_sets_of_eConn_eq_one (hPconn : P.eConn = 1) (hX : X ⊆ M.E) :
    M.Indep X ↔ (M.Indep (X ∩ P i)) ∧ (M.Indep (X ∩ P !i)) ∧
    ((M ／ (P i)).Indep (X ∩ (P !i)) ∨ (M ／ (P !i)).Indep (X ∩ (P i))) := by
  constructor
  · intro h₁
    simp only [Indep.subset (h₁) (show (X ∩ P i) ⊆ X by simp),
      Indep.subset (h₁) (show (X ∩ P ! i) ⊆ X by simp), true_and]
    sorry
  · intro h
    rcases h with ⟨h₁, h₂, h₃⟩
    by_contra! hc
    rw [not_indep_iff, dep_iff_superset_isCircuit] at hc
    obtain ⟨C, hc₁, hc₂⟩ := hc
    have h : ∀ j : Bool, ¬Disjoint C (P j) := by
      by_contra! hc
      obtain ⟨j, hcj⟩ := hc
      rw [Separation.disjoint_true_iff_subset_false] at hcj
      · have : C ⊆ X ∩ (P !j) := by grind
        have : M.Dep (X ∩ (P !j)) := by
          rw [dep_iff_superset_isCircuit (show X ∩ (P !j) ⊆ M.E by grind)]
          use C
        by_cases hi : i = j
        rw [← hi, dep_iff] at this
        grind
        rw [← Bool.not_not j, Bool.not_eq_not] at hi
        rw [← hi, dep_iff] at this
        grind
      · refine subset_trans (hc₁) (hX)

      -- rw [indep_iff_forall_subset_not_isCircuit] at h₁
      -- have h₄ : ∃ C ⊆ X ∩ P !j, M.IsCircuit C := by
      --   use C
      --   simp [hc₁, hc₂]
      --   rw [← Bool.not_not (j), ← Separation.compl_eq] at hcj
      -- sorry
      -- sorry
      -- sorry
    sorry

variable [DecidableEq α]

lemma IsMinor.contract_max_skew_of_eConn_eq_one (hPconn : P.eConn = 1)
    (hX : (M ／ (P !i)).IsBase X) (hx : x ∈ (P i) \ X)
    (hY : (M ／ (P !i)).IsBase Y) (hy : y ∈ (P i) \ Y) :
    M ／ Y ＼ ((P i) \ (insert y Y))
    = mapEquiv (M ／ X ＼ ((P i) \ (insert x X))) (Equiv.swap x y) := by
  sorry

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
  --- At this point we want to show that P has a "small side" relative to a copy of N,
  --- that is, for a fixed copy of N, there is a side of P that contains at most one
  --- element of that copy. Now this small side cannot have rank 1, because M is simple.
  --- It cannot have corank 1, because then e would be in a triad, and e is a
  --- deletable element. So by a lemma, the small side contains a "flexible" element, f, meaning
  --- that both M \ f and M / f have isomorphic copies of N. The hypotheses imply
  --- f is in no triangle and in no triad, so that si(M/f) = M/f and co(M\f) = M\f.
  --- Now we can apply Bixby to f and deduce that the splitter theorem holds.
  sorry


--  Scraps from this point onward

--

-- lemma IsMinor.exists_smallside_of_eConn_eq_zero {N : Matroid α} (hNM : N ≤m M)
--     (hN : N.TutteConnected 2) (hPconn : P.eConn = 0) :
--     ∃ i, (P i ∩ N.E) = ∅ := by
--   by_contra! hcon₁
--   have hNnonem : N.Nonempty := by
--     by_contra! hcon₂
--     rw [← ground_nonempty_iff, not_nonempty_iff_eq_empty] at hcon₂
--     rw [hcon₂] at hcon₁
--     simp_all only [inter_empty, Set.not_nonempty_empty, forall_const]
--   have hj : ∀ j : Bool, ∃ e, e ∈ (P j ∩ N.E) := by
--     intro j
--     specialize hcon₁ (i := j)
--     rw [nonempty_def] at hcon₁
--     obtain ⟨e, he⟩ := hcon₁
--     use e
--   have hNconn : (P.induce hNM.subset).eConn = 0 := by
--     rw [← ENat.lt_one_iff_eq_zero, show (1 : ℕ∞) = 0 + 1 from rfl, ENat.lt_add_one_iff]
--     grw [eConn_induce_le_of_isMinor _ hNM, hPconn]
--     simp
--   rw [tutteConnected_two_iff] at hN
--   have hNP := hN.trivial_of_eConn_eq_zero hNconn
--   rw [Separation.trivial_def, induce_apply, induce_apply] at hNP
--   obtain hPf | hPt := hNP
--   specialize hj (j := false)
--   grind
--   specialize hj (j := true)
--   grind

--

-- lemma IsMinor.exists_smallside_of_eConn_eq_one {N : Matroid α} (hNM : N ≤m M)
--     (hN : N.TutteConnected 3) (hPcon : P.eConn = 1) :
--     ∃ i, (P i ∩ N.E).Subsingleton := by
--   by_contra! hc
--   rw [show (3 : ℕ∞) = 2 + 1 by grind, tutteConnected_iff_forall] at hN
--   specialize hN (P:= P.induce hNM.subset)
--   have h : (P.induce hNM.subset).eConn + 1 ≤ 2 := by
--     grw [eConn_induce_le_of_isMinor P]
--     · apply le_of_eq at hPcon
--       rw [← ENat.add_one_le_add_one_iff, one_add_one_eq_two] at hPcon
--       exact hPcon
--     · exact hNM
--   apply hN at h
--   rw [isTutteSeparation_iff_lt_encard] at h
--   · push_neg at h
--     obtain ⟨i, hi⟩ := h
--     specialize hc (i:= i)
--     grw [eConn_induce_le_of_isMinor P, hPcon] at hi
--     · rw [← Set.one_lt_encard_iff_nontrivial] at hc
--       rw [← induce_apply P hNM.subset] at hc
--       grw [hi] at hc
--       tauto
--     · exact hNM
--   · rw [← lt_top_iff_ne_top]
--     grw [eConn_induce_le_of_isMinor, hPcon]
--     · simp [ENat.one_lt_top]
--     · exact hNM

--

-- lemma exists_deletable_contractible_of_smallside {N : Matroid α} (hNM : N ≤m M)
--     (hN : N.TutteConnected 3) (hPcon : P.eConn = 1) (hPN : (P i ∩ N.E).Subsingleton)
--     (hPr : 2 ≤ M.eRk (P i)) (hPcr : 2 ≤ M✶.eRk (P i)) :
--     ∃ e ∈ P i, M.IsDeletable N e ∧ M.IsContractible N e := by
--   have hN2 : N.TutteConnected 2 := hN.mono (by norm_num)
--   by_contra! hcon₁
--   have hM : M.TutteConnected (1 + 1) := by
--     by_contra! hcon₂
--     rw [not_tutteConnected_iff_exists] at hcon₂
--     obtain ⟨Q, hQ⟩ := hcon₂
--     nth_rw 2 [show (1 : ℕ∞) = 0 + 1 from rfl] at hQ
--     rw [ENat.add_one_le_add_one_iff] at hQ
--     sorry
--   sorry

--

-- lemma IsMinor.preserve_minor_of_eConn_eq_one {N : Matroid α} (hNM : N ≤m M) (hM : M.Connected)
--     (hN : N.TutteConnected 3) (hP : P.IsTutteSeparation) (hPcon : P.eConn = 1)
--     (hPN : (P i ∩ N.E).Subsingleton) : ∀ e ∈ P i, ((M ＼ {e}).Connected → M.IsDeletable N e) ∧
--     ((M ／ {e}).Connected → M.IsContractible N e) := by sorry
