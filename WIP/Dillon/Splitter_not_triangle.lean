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

variable {α β : Type*} {e f x y: α} {i j : Bool} {k : ℕ∞} {X Y : Set α}
    {M : Matroid α} {N : Matroid β} {P : M.Separation}

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

-- lemma IsMinor.preserve_minor_of_eConn_eq_one {N : Matroid α} (hNM : N ≤m M) (hM : M.Connected)
--     (hN : N.TutteConnected 3) (hP : P.IsTutteSeparation) (hPcon : P.eConn = 1)
--     (hPN : (P i ∩ N.E).Subsingleton) : ∀ e ∈ P i, ((M ＼ {e}).Connected → M.IsDeletable N e) ∧
--     ((M ／ {e}).Connected → M.IsContractible N e) := by sorry
