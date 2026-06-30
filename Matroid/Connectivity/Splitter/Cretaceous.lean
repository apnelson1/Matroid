import Mathlib.Data.Set.Defs
import Mathlib.Logic.Equiv.Basic
import Mathlib.Combinatorics.Matroid.Minor.Order
import Mathlib.Combinatorics.Matroid.Map
import Matroid.ForMathlib.Set
import Matroid.Connectivity.Separation.Two
import Matroid.Triangle
import Matroid.Constructions.Small
import Matroid.Uniform.Minor

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

lemma IsMinor.exists_smallside_of_separation {N : Matroid α} (hNM : N ≤m M)
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

-- lemma exists_flexible {N : Matroid α} (hM : M.TutteConnected 2) (hsi : M.Simple) (hsi' : M✶.Simple)
--     (hP : P.IsTutteSeparation) (hPconn : P.eConn ≤ 1) (hNM : N ≤m M) (hN : N.Loopless)
--     (hN' : N.Coloopless) (hss : ((P !i) ∩ N.E).Subsingleton) :
--     ∃ e, ∀ b, Nonempty (N ≤i M.remove b {e}) := by
--   obtain hlt | hPconn := hPconn.lt_or_eq
--   · exact False.elim <| hM.not_isTutteSeparation (k := 1) (Order.add_one_le_of_lt hlt) hP
--   rw [← three_le_girth_iff] at hsi hsi'
--   obtain ⟨e, he, heg, hecg⟩ := hM.exists_notMem_guts_notMem_coguts hP hsi hsi' hPconn.le (!i)
--   refine ⟨e, fun i ↦ ?_⟩
--   obtain rfl | rfl := i
--   · exact P.isoMinor_delete_of_notMem_coguts hPconn hNM hN hN' hss (by grind) hecg
--   exact P.isoMinor_contract_of_notMem_guts hPconn hNM hN hN' hss (by grind) heg

/-- If `M ＼ {e}` has `N` as a minor, and is cosimple but not `3`-connected, then it has a
flexible element. -/
lemma exists_flexible {N : Matroid α} (hM : M.TutteConnected 3) (h4 : 4 ≤ M.E.encard)
    (hMe : ¬ (M ＼ {e}).TutteConnected 3) (hsi' : (M ＼ {e})✶.Simple)
    (hNM : N ≤m M ＼ {e}) (hN : N.TutteConnected 3) (hnt : N.E.Nontrivial) :
      ∃ f, ∀ b, Nonempty (N ≤i M.remove b {f}) := by
  rw [show (3 : ℕ∞) = 1 + 1 + 1 from rfl] at *
  have hM2 : (M ＼ {e}).TutteConnected (1 + 1) := (hM.deleteElem (e := e) (by enat_to_nat!; lia))
  obtain ⟨P, hPconn, hP⟩ := hM2.exists_of_not_tutteConnected_add_one hMe
  rw [ENat.add_one_inj] at hPconn
  have hsi := (hM.simple h4).delete {e}
  rw [← three_le_girth_iff] at hsi hsi'
  obtain ⟨i, hi⟩ := hN.exists_subsingleton_of_isTutteSeparation (P := P.induce N)
    (by grw [← hPconn, P.eConn_induce_le_of_isMinor hNM])
  obtain ⟨f, hf, hfg, hfcg⟩ := hM2.exists_notMem_guts_notMem_coguts hP hsi hsi' hPconn.le i
  use f
  have hNl := hN.loopless (le_self_add ..) hnt
  have hNcl := hN.coloopless (le_self_add ..) hnt
  rw [induce_apply_subset _ hNM.subset] at hi
  rintro (rfl | rfl)
  · obtain ⟨φ⟩ := P.isoMinor_delete_of_notMem_coguts hPconn hNM hNl hNcl (i := !i)
      (by simpa using hi) (by grind) hfcg
    refine ⟨φ.trans_isMinor ?_⟩
    simp only [delete_delete, union_singleton, remove_false]
    exact delete_isMinor_delete_of_subset _ (by simp)
  obtain ⟨φ⟩ := P.isoMinor_contract_of_notMem_guts hPconn hNM hNl hNcl (i := !i)
    (by simpa using hi) (by grind) hfg
  exact ⟨φ.trans_isMinor ((delete_isMinor ..).contract_isMinor_contract (by grind))⟩


  -- have := exists_flexible hM2 ((hM.simple h4).delete _) hsi' hP
--   _

-- (hsi : M.Simple) (hsi' : M✶.Simple)
--     (hP : P.IsTutteSeparation) (hPconn : P.eConn ≤ 1) (hNM : N ≤m M) (hN : N.Loopless)
--     (hN' : N.Coloopless) (hss : ((P !i) ∩ N.E).Subsingleton) :
--     ∃ e, ∀ b, Nonempty (N ≤i M.remove b {e}) := by

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
