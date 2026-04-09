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

variable {α β : Type*} {e f x y : α} {X Y C D : Set α} {i j k l : Bool} {k : ℕ∞}
    {M : Matroid α} {N : Matroid β} {P : M.Separation}

theorem splitter_theorem (hM : M.TutteConnected 3) (hN : N.TutteConnected 3) (fNM : N <i M)
    (hNT : ¬ N.Triassic) : ∃ e, (M.IsDeletable N e ∧ (M ＼ {e}).TutteConnected 3)
    ∨ (M.IsContractible N e ∧ (M ／ {e}).TutteConnected 3) := by
  sorry

lemma IsMinor.exists_smallside_of_separation {N : Matroid α} (hNM : N ≤m M)
    (hN : N.TutteConnected (k + 2)) (hPconn : P.eConn = k) : ∃ i, (P i ∩ N.E).encard ≤ k := by
  by_contra! hc₁
  have htop : k ≠ ⊤ := by
    by_contra! hc₂
    rw [hc₂] at hc₁
    simp [not_top_lt] at hc₁
  rw [show k+2 = k+1+1 by grind, tutteConnected_iff_forall] at hN
  specialize hN (P := P.induce N)
  refine hN (?_) (?_)
  · grw [eConn_induce_le_of_isMinor P hNM, hPconn]
  · rw [isTutteSeparation_iff_lt_encard]
    · intro i
      rw [induce_apply_subset _ hNM.subset]
      specialize hc₁ (i := i)
      grw [eConn_induce_le_of_isMinor P hNM]
      grind
    · rw [← lt_top_iff_ne_top]
      grw [eConn_induce_le_of_isMinor P hNM, hPconn]
      rwa [lt_top_iff_ne_top]

lemma IsMinor.delete_subset_separator (hPconn : P.eConn = 0) (hX : X ⊆ P i) :
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
    (hPconn : P.eConn = 0) (hPi : Disjoint (P i) N.E) : N ≤m M ＼ P i := by
  refine hNM.isMinor_of_eConn_eq_zero (X := P (!i)) (delete_isMinor ..) ?_ (by simp) (by simpa)
  rwa [← disjoint_iff_subset_not hNM.subset, disjoint_comm]

lemma IsMinor.isMinor_contract_smallside_of_eConn_eq_zero {N : Matroid α} (hNM : N ≤m M)
    (hPconn : P.eConn = 0) (hPi : Disjoint (P i) N.E) : N ≤m M ／ P i := by
  have aux := hNM.dual.isMinor_delete_smallside_of_eConn_eq_zero (P := P.induce M✶) (i := i)
    (by simpa) (by simpa)
  simpa using aux.dual

lemma IsMinor.isMinor_deleteElem_smallside_of_eConn_eq_zero {N : Matroid α} (hNM : N ≤m M)
    (hPconn : P.eConn = 0) (hPi : Disjoint (P i) N.E) (he : e ∈ P i) : N ≤m M ＼ {e}  := by
  have h₁ : N ≤m M ＼ P i := isMinor_delete_smallside_of_eConn_eq_zero hNM hPconn hPi
  have h₂ : M ＼ P i ≤m M ＼ {e} := by
    refine IsMinor.delete_isMinor_delete_of_subset (by simp [IsMinor.refl]) ?_ (by simp)
    rwa [singleton_subset_iff]
  refine IsMinor.trans h₁ h₂

lemma IsMinor.isMinor_contractElem_smallside_of_eConn_eq_zero {N : Matroid α} (hNM : N ≤m M)
    (hPconn : P.eConn = 0) (hPi : Disjoint (P i) N.E) (he : e ∈ P i) : N ≤m M ／ {e}  := by
  have aux := hNM.dual.isMinor_deleteElem_smallside_of_eConn_eq_zero (P := P.induce M✶) (i := i)
      (by simpa) (by simpa) (by simpa)
  rwa [← dual_contract, dual_isMinor_iff] at aux

/-
Let `N` be a `3`-connected minor of `M` and `P` be a `(1 + 1)`-separation of `M`,
where `(N.E \ P i).Subsingleton`. (i.e. `N` is mostly contained in `P i`).
Say `P i \ N.E = {e}`.
Then there is a minor `N'` with ground set `insert e (P i)` such that `N ≤m N' ≤m M`.
This should be useful, and can be found with the lemma
`IsMinor.exists_isMinor_of_subset_subset`.
-/
-- = mapEquiv (M ／ X ＼ ((P i) \ (insert x X))) (Equiv.swap x y) := by

/-- Replace this with `Dep.of_isMinor_of_subset`. -/

lemma Dep.of_minor_disjoint {N : Matroid α} (hNM : N ≤m M) (hX : X ⊆ N.E) :
    M.Dep X → N.Dep X := by
  apply IsMinor.exists_contract_indep_delete_coindep at hNM
  obtain ⟨C, D, hC, hD, hCD, hCDN⟩ := hNM
  subst hCDN
  intro h₁
  have h₂ : (M ／ C).Dep X := Dep.contract_of_disjoint (h₁) (by grind)
  apply Dep.delete_of_disjoint (h₂) (by grind)

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

lemma Circuit.nonempty_circuit_union_of_independent (hX : M.Indep X)
    (hC : M.IsCircuit C) (hCXP : C ⊆ X ∪ D) : (C ∩ D).Nonempty := by
  rw [indep_iff_forall_subset_not_isCircuit] at hX
  specialize hX (C := C)
  by_contra! hc
  rw [← disjoint_iff_inter_eq_empty] at hc
  have aux := Disjoint.subset_left_of_subset_union hCXP hc
  apply hX at aux
  contradiction

lemma Separation.unique_circuit_of_eConn_le_one {C : Bool → Set α}
    (hC : ∀ j, (M ↾ (X ∪ (P i))).IsCircuit (C j)) (hX : (M ↾ (P !i)).Indep X)
    (hPconn : P.eConn ≤ 1) (he : ∀ j, (C j ∩ X).Nonempty) : ((C true) ∩ X) = ((C false) ∩ X) := by
  rw [restrict_indep_iff] at hX
  have hCX : ∀ j, (C j) ∩ (P !i) = (C j) ∩ X := by grind
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
    by_cases aux : k = i
    · subst aux
      refine Circuit.nonempty_circuit_union_of_independent (hX.1) ((hC j).1) ((hC j).2)
    · rw [← ne_eq, ← Bool.not_eq, Bool.not_eq_eq_eq_not] at aux
      rw [aux, hCX j]
      exact he j
  clear he
  have hC₂ : ∀ j k, M.IsCircuit (((C j) ∩ X) ∪ ((C k) ∩ (P i))) := by
    intro j k
    rw [← hCX j]
    have aux := Separation.isCircuit_union_inter_of_eConn_le_one_bool
        hC₁ hPconn heCP (!i) (j) (k)
    rwa [Bool.not_not] at aux
  clear hCX hC₁
  by_contra! hcon
  have hx : ∃ x, x ∈ (C true ∩ X) \ (C false ∩ X) := by
    rw [← nonempty_def, diff_nonempty, subset_iff_ssubset_or_eq, not_or]
    constructor
    · have : ¬((C true) ∩ X) ⊂ ((C false) ∩ X) := by
        have := IsCircuit.not_ssubset (hC₂ false true) (hC₂ true true)
        grind only [→ Indep.subset_ground, = subset_def, !Separation.disjoint_bool, = ssubset_def,
          = disjoint_left, → IsCircuit.subset_ground, = mem_inter_iff, = mem_union]
      grind only [#53bc]
    · exact hcon
  clear hcon
  obtain ⟨x, hx₁⟩ := hx
  obtain ⟨y, hy₁, hy₂⟩ := heCP true i
  obtain ⟨D₁, hD₁, hD₂, hD₃⟩ := IsCircuit.strong_elimination
      ((hC true).1) (hC₂ false true) (hy₁) (by grind) (by grind)
      (show x ∉ (C false ∩ X) ∪ (C true ∩ (P i)) by grind)
  have hD₄ : ∀ j, (D₁ ∩ (P j)).Nonempty := by
    intro j
    by_cases! aux : j = i
    rw [aux]
    refine Circuit.nonempty_circuit_union_of_independent (hX.1) (hD₂) (show D₁ ⊆ X ∪ P i by grind)
    rw [← Bool.not_eq, Bool.not_eq_eq_eq_not] at aux
    rw [aux, nonempty_def]
    use x
    rw [mem_inter_iff]
    constructor
    · exact hD₃
    · rw [mem_diff, mem_inter_iff] at hx₁
      refine mem_of_subset_of_mem (hX.2) hx₁.1.2
  clear hx₁ hD₃
  have hD₃ := Separation.isCircuit_union_inter_of_eConn_le_one ((hC true).1) (hD₂) (hPconn)
      (heCP true) (hD₄) (!i)
  rw [Bool.not_not] at hD₃
  have hcon : ((C true ∩ P !i) ∪ D₁ ∩ P i) ⊂ C true := by grind
  have := IsCircuit.not_ssubset ((hC true).1) (hD₃)
  contradiction

lemma IsMinor.contract_disjoint_base_of_eConn_eq_one {N : Matroid α} (hPconn : P.eConn ≤ 1)
    (hN : N.TutteConnected 3) (hNM : N ≤m M) (hPi: (N.E ∩ (P !i)).Subsingleton) :
    ∃ X, (M ／ (P i)).IsBase X ∧ N ≤m (M ／ X) := by

  /-
  Let x be a subsingleton set such that (P !i) \ x is disjoint with N.E.
  Let C, D be a partition of (P !i) \ x such that C is independent, D is dependent, and
  N is a minor of M / C \ D.
  The Separation.unique_circuit_of_eConn_le_one lemma implies that there is a subsingleton
  set y such that C \ y is independent in M / P i.
  Let B be a basis of M / P i \ x that contains C \ y.
  We want to show that we can contract B from M and obtain an N minor.
  We accomplish this by showing that in M / (C \ y), we have skewness between B \ C and P i,
  so we are free to contract B \ C instead of deleting it.
  -/

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

--  Scraps from this point onward

/-

lemma IsMinor.exists_smallside_of_eConn_eq_zero {N : Matroid α} (hNM : N ≤m M)
    (hN : N.TutteConnected 2) (hPconn : P.eConn = 0) :
    ∃ i, (P i ∩ N.E) = ∅ := by
  by_contra! hcon₁
  have hNnonem : N.Nonempty := by
    by_contra! hcon₂
    rw [← ground_nonempty_iff, not_nonempty_iff_eq_empty] at hcon₂
    rw [hcon₂] at hcon₁
    simp_all only [inter_empty, Set.not_nonempty_empty, forall_const]
  have hj : ∀ j : Bool, ∃ e, e ∈ (P j ∩ N.E) := by
    intro j
    specialize hcon₁ (i := j)
    rw [nonempty_def] at hcon₁
    obtain ⟨e, he⟩ := hcon₁
    use e
  have hNconn : (P.induce hNM.subset).eConn = 0 := by
    rw [← ENat.lt_one_iff_eq_zero, show (1 : ℕ∞) = 0 + 1 from rfl, ENat.lt_add_one_iff]
    grw [eConn_induce_le_of_isMinor _ hNM, hPconn]
    simp
  rw [tutteConnected_two_iff] at hN
  have hNP := hN.trivial_of_eConn_eq_zero hNconn
  rw [Separation.trivial_def, induce_apply, induce_apply] at hNP
  obtain hPf | hPt := hNP
  specialize hj (j := false)
  grind
  specialize hj (j := true)
  grind

lemma IsMinor.exists_smallside_of_eConn_eq_one {N : Matroid α} (hNM : N ≤m M)
    (hN : N.TutteConnected 3) (hPcon : P.eConn = 1) :
    ∃ i, (P i ∩ N.E).Subsingleton := by
  by_contra! hc
  rw [show (3 : ℕ∞) = 2 + 1 by grind, tutteConnected_iff_forall] at hN
  specialize hN (P:= P.induce hNM.subset)
  have h : (P.induce hNM.subset).eConn + 1 ≤ 2 := by
    grw [eConn_induce_le_of_isMinor P]
    · apply le_of_eq at hPcon
      rw [← ENat.add_one_le_add_one_iff, one_add_one_eq_two] at hPcon
      exact hPcon
    · exact hNM
  apply hN at h
  rw [isTutteSeparation_iff_lt_encard] at h
  · push_neg at h
    obtain ⟨i, hi⟩ := h
    specialize hc (i:= i)
    grw [eConn_induce_le_of_isMinor P, hPcon] at hi
    · rw [← Set.one_lt_encard_iff_nontrivial] at hc
      rw [← induce_apply P hNM.subset] at hc
      grw [hi] at hc
      tauto
    · exact hNM
  · rw [← lt_top_iff_ne_top]
    grw [eConn_induce_le_of_isMinor, hPcon]
    · simp [ENat.one_lt_top]
    · exact hNM

lemma exists_deletable_contractible_of_smallside {N : Matroid α} (hNM : N ≤m M)
    (hN : N.TutteConnected 3) (hPcon : P.eConn = 1) (hPN : (P i ∩ N.E).Subsingleton)
    (hPr : 2 ≤ M.eRk (P i)) (hPcr : 2 ≤ M✶.eRk (P i)) :
    ∃ e ∈ P i, M.IsDeletable N e ∧ M.IsContractible N e := by
  have hN2 : N.TutteConnected 2 := hN.mono (by norm_num)
  by_contra! hcon₁
  have hM : M.TutteConnected (1 + 1) := by
    by_contra! hcon₂
    rw [not_tutteConnected_iff_exists] at hcon₂
    obtain ⟨Q, hQ⟩ := hcon₂
    nth_rw 2 [show (1 : ℕ∞) = 0 + 1 from rfl] at hQ
    rw [ENat.add_one_le_add_one_iff] at hQ
    sorry
  sorry

lemma IsMinor.preserve_minor_of_eConn_eq_one {N : Matroid α} (hNM : N ≤m M) (hM : M.Connected)
    (hN : N.TutteConnected 3) (hP : P.IsTutteSeparation) (hPcon : P.eConn = 1)
    (hPN : (P i ∩ N.E).Subsingleton) : ∀ e ∈ P i, ((M ＼ {e}).Connected → M.IsDeletable N e) ∧
    ((M ／ {e}).Connected → M.IsContractible N e) := by sorry

-/
