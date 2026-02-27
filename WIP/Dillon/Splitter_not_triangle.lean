import Mathlib.Data.Set.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Combinatorics.Matroid.Minor.Order
import Mathlib.Combinatorics.Matroid.Map
import Matroid.ForMathlib.Set
import Matroid.Triangle

open Set Matroid Function Separation

-- lemma Equiv.swap_eqOn_compl {α : Type*} [DecidableEq α] (x y : α) :
--     EqOn (Equiv.swap x y) (Equiv.refl α) {x, y}ᶜ :=
--   fun a ha ↦ by grind

-- lemma Equiv.swap_image_eq_self

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
  specialize hN (P:= P.induce N)
  refine hN (?_) (?_)
  · grw [eConn_induce_le_of_isMinor P hNM, hPconn]
  · rw [isTutteSeparation_iff_lt_encard]
    · intro i
      rw [induce_apply_subset _ hNM.subset]
      specialize hc (i:= i)
      grw [eConn_induce_le_of_isMinor P hNM]
      grind
    · rw [← lt_top_iff_ne_top]
      grw [eConn_induce_le_of_isMinor P hNM, hPconn]
      rwa [lt_top_iff_ne_top]

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

lemma Separation.indep_of_contract {I} (hI : I ⊆ M.E) (hi : M.Indep (I ∩ P i))
    (hic : (M ／ P i).Indep (I ∩ P (!i))) : M.Indep I := by
  replace hic := hic.of_isMinor <|
    contract_isMinor_of_subset _ (show I ∩ P i ⊆ P i from inter_subset_right)
  rw [hi.contract_indep_iff, union_comm, P.union_inter_left _] at hic
  exact hic.2

lemma Indep.exists_indep_contract_inter_of_eConn_le_one {I} (hI : M.Indep I) (hP : P.eConn ≤ 1) :
    ∃ i, (M ／ P i).Indep (I ∩ P (!i)) := by
  wlog hIb : M.IsBase I generalizing I with aux
  · obtain ⟨B, hB, hIB⟩ := hI.exists_isBase_superset
    obtain ⟨i, hi⟩ := aux hB.indep hB
    exact ⟨i, hi.subset <| by grind⟩
  -- extend each `I ∩ P i` to a basis `J i` of `P i`.
  choose J hJ using fun j ↦ (hI.inter_right (P j)).subset_isBasis_of_subset inter_subset_right
  have hb {j} : M.IsBasis (J j) (P j) := (hJ j).1
  have hss {j} : I ∩ P j ⊆ J j := (hJ j).2
  -- Using the definition of connectivity, we get that `∪ J` isn't much bigger than `I`.
  have hcard : (J false \ I).encard + (J true \ I).encard ≤ 1 := by
    rwa [← P.eConn_eq false, (hJ false).1.eConn_eq (J := J true) (by simpa using (hJ true).1),
      nullity_eq_nullity_add_encard_diff (X := I), hI.nullity_eq, zero_add,
      union_diff_distrib, encard_union_eq] at hP
    · grw [hb.subset, hb.subset, diff_subset, diff_subset]
      exact P.disjoint_false_true
    · grw [← P.union_inter_left _ hI.subset_ground false, Bool.not_false, hss, hss]
    grw [hb.indep.subset_ground, hb.indep.subset_ground, union_self, hIb.closure_eq]
  -- In fact, there is some `i` for which `J i` is no bigger.
  obtain ⟨i, hi⟩ : ∃ i, (J i \ I) = ∅ := by
    by_contra! hcon
    grw [← one_le_encard_iff_nonempty.2 (hcon _), ← one_le_encard_iff_nonempty.2 (hcon _)] at hcard
    simp at hcard
  -- this is the right `i`.
  rw [diff_eq_empty] at hi
  refine ⟨i, ?_⟩
  rw [hb.contract_indep_iff, and_iff_left <| (P.disjoint_bool i).mono_right inter_subset_right]
  exact hI.subset <| union_subset inter_subset_left hi

lemma Separation.indep_iff_of_eConn_le_one {I} (hP : P.eConn ≤ 1) (hIE : I ⊆ M.E := by aesop_mat) :
    M.Indep I ↔ ((∀ i, M.Indep (I ∩ P i)) ∧ (∃ i, (M ／ P i).Indep (I ∩ P (!i)))) :=
  ⟨fun h ↦ ⟨fun _ ↦ h.inter_right _, h.exists_indep_contract_inter_of_eConn_le_one hP⟩,
    fun ⟨h, i, h'⟩ ↦ P.indep_of_contract hIE (h i) h'⟩

lemma IsMinor.indep_iff_indep {I : Set α} (hX : (M ／ (P i)).IsBase X) (hY : (M ／ (P i)).IsBase Y)
    (hI : I ⊆ P i) : (M ／ X).Indep I ↔ (M ／ Y).Indep I := by
  by_cases hIi : M.Indep I
  · rw [hX.indep.of_contract.contract_indep_iff, disjoint_comm, union_comm,
      ← hIi.contract_indep_iff, hY.indep.of_contract.contract_indep_iff, disjoint_comm,
      union_comm, ← hIi.contract_indep_iff]
    exact iff_of_true (hX.indep.of_isMinor (contract_isMinor_of_subset _ hI))
      (hY.indep.of_isMinor (contract_isMinor_of_subset _ hI))
  exact iff_of_false (fun h ↦ hIi h.of_contract) (fun h ↦ hIi h.of_contract)


-- lemma g1 (P : M.Separation) (i : Bool) : Disjoint (P i) (P !i) := sorry
-- @[grind! .]
-- lemma g1' (P : M.Separation) {i : Bool} : Disjoint (P i) (P !i) := sorry
-- @[grind! =>]
-- lemma g2 (P : M.Separation) : ∀ i, P i ⊆ M.E := sorry
-- @[grind! =>]
-- lemma g3 (P : M.Separation) (i : Bool) (he : e ∈ M.E) : e ∈ P i ↔ e ∉ P !i := sorry
-- @[grind! =>]
-- lemma g4 (P : M.Separation) (i : Bool) (he : e ∈ M.E) : e ∉ P i ↔ e ∈ P !i := sorry
-- @[grind! =>]
-- lemma g5 (P : M.Separation) (i : Bool) (he : e ∈ P i) : e ∉ P !i := sorry
-- @[grind! =>]
-- lemma g6 (P : M.Separation) (i : Bool) (he : e ∈ P i) : e ∉ P !i := sorry


-- attribute [grind ->] IsBase.subset_ground


lemma IsMinor.contract_insert_indep_iff (hPconn : P.eConn = 1) {I : Set α}
    (hX : (M ／ (P i)).IsBase X) (he : e ∈ (P !i)) (heX : e ∉ M.closure X)
    (hY : (M ／ (P i)).IsBase Y) (hf : f ∈ (P !i)) (hfY : f ∉ M.closure Y) (hI : I ⊆ P i) :
    (M ／ X).Indep (insert e I) ↔ (M ／ Y).Indep (insert f I) := by
  wlog hi : (M ／ X).Indep (insert e I) generalizing X Y e f with aux
  · exact iff_of_false hi fun h ↦ hi <| (aux hY hf hfY hX he heX h).1 h
  refine iff_of_true hi ?_
  rw [hX.indep.of_contract.contract_indep_iff] at hi
  obtain ⟨j, hj⟩ := hi.2.exists_indep_contract_inter_of_eConn_le_one hPconn.le
  obtain rfl | rfl := j.eq_or_eq_not i
  · grind [hX.eq_of_subset_indep hj (by grind)]
  rw [hY.indep.of_contract.contract_indep_iff, disjoint_insert_left,
    and_iff_right (by grind [P.disjoint_bool i])]
  refine P.indep_of_contract (i := !i) (by grind [P.subset' i]) ?_ (hj.subset (by grind))
  suffices h : M.Indep (insert f Y) from h.subset <| by grind
  grind [hY.indep.of_contract.insert_indep_iff]

lemma IsMinor.eq_mapEquiv [DecidableEq α] (hPconn : P.eConn = 1)
    (hX : (M ／ (P i)).IsBase X) (hx : x ∈ (P !i)) (hxX : x ∉ M.closure X)
    (hY : (M ／ (P i)).IsBase Y) (hy : y ∈ (P !i)) (hyY : y ∉ M.closure Y) :
    (M ／ Y) ↾ (insert y (P i)) = ((M ／ X) ↾ (insert x (P i))).mapEquiv (Equiv.swap x y) := by
  have hxi : x ∉ P i := by rwa [P.not_mem_iff_mem_not]
  have hyi : y ∉ P i := by rwa [P.not_mem_iff_mem_not]
  refine ext_indep ?_ fun I hI ↦ ?_
  · simp only [restrict_ground_eq, mapEquiv_ground_eq, image_insert_eq, Equiv.swap_apply_left]
    rw [Equiv.swap_image_eq_self]
    exact iff_of_false hxi hyi
  simp only [restrict_ground_eq] at hI
  rw [restrict_indep_iff, mapEquiv_indep_iff, restrict_indep_iff, Equiv.symm_swap, and_iff_left hI]
  -- if `x = y`, this implies the result.
  obtain rfl | hne := eq_or_ne x y
  · simp only [Equiv.swap_self, Equiv.refl_apply, image_id', hI, and_true]
    by_cases hxI : x ∈ I
    · rw [← insert_diff_self_of_mem hxI,
        IsMinor.contract_insert_indep_iff hPconn hX hx hxX hY hy hyY (by grind)]
    rw [IsMinor.indep_iff_indep hX hY (I := I) (by grind)]
  -- otherwise, the previous lemma does it.
  by_cases hyI : y ∈ I
  · rw [Equiv.swap_comm, Equiv.swap_image_eq_exchange hyI, and_iff_left (by grind),
      ← IsMinor.contract_insert_indep_iff (X := Y) (e := y) hPconn hY hy hyY hX hx hxX (by grind),
      insert_diff_self_of_mem hyI]
    exact notMem_subset hI <| by grind
  have hxI : x ∉ I := by grind
  rw [Equiv.swap_image_eq_self (iff_of_false hxI hyI), and_iff_left (by grind),
    IsMinor.indep_iff_indep hX hY (by grind)]









    -- = mapEquiv (M ／ X ＼ ((P i) \ (insert x X))) (Equiv.swap x y) := by

lemma IsMinor.contract_max_skew_of_eConn_eq_one [DecidableEq α] (hPconn : P.eConn = 1)
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
