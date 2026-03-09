import Matroid.Connectivity.Minor
import Matroid.Connectivity.Connected
import Matroid.Connectivity.Separation.Basic
import Matroid.ForMathlib.Matroid.Constructions
import Matroid.Triangle


/-
This file contains miscellaneous lemmas about triangles/triads and connectivity that are not
explicitly about fans.
-/

variable {α : Type*} {M : Matroid α} {e f g a b c d : α} {T T' C K X : Set α}

open Set Function

namespace Matroid


/- If `e, f` is a series pair contained in a triangle of a connected matroid, then we can
remove both and stay connected. -/
lemma Connected.contract_delete_connected_of_mem_triangle_of_series {T} (hM : M.Connected)
    (hT : M.IsTriangle T) (heT : e ∈ T) (hfT : f ∈ T) (hef : e ≠ f) (h_series : M✶.Parallel e f) :
    (M ／ {e} ＼ {f}).Connected := by
  have hMnt := hT.nontrivial.mono hT.subset_ground
  have hnt' := ((hT.nontrivial_diff_singleton e).mono
    (diff_subset_diff_left hT.subset_ground))
  obtain ⟨g, hge, hgf, rfl⟩ :=
    exists_eq_of_encard_eq_three_of_mem_of_mem hT.three_elements heT hfT hef
  obtain hd | hc := hM.delete_or_contract hMnt e
  · rw [← connected_dual_iff] at hd
    refine False.elim <| ((hd.loopless hnt').isNonloop_of_mem (e := f) ?_).not_isLoop ?_
    · simp only [dual_delete, contract_ground, dual_ground, mem_diff, mem_singleton_iff]
      grind
    exact dual_delete .. ▸ h_series.isLoop_contractElem hef
  refine (hc.delete_or_contract hnt' f).elim id fun hd ↦ ?_
  obtain hss | hnt := (M ／ {e} ／ {f}).E.subsingleton_or_nontrivial
  · convert singleton_connected (M := M ／ {e} ＼ {f}) (e := g) ?_
    exact hss.eq_singleton_of_mem <| by grind
  simpa [hT.swap_left.mem_closure₃] using (hd.loopless hnt).isNonloop_of_mem (e := g) (by grind)

/- If `e, f` is a parallel pair contained in a triad of a connected matroid, then we can
remove both and stay connected. -/
lemma Connected.contract_delete_connected_of_mem_triad_of_parallel {T} (hM : M.Connected)
    (hT : M.IsTriad T) (heT : e ∈ T) (hfT : f ∈ T) (hef : e ≠ f) (h_para : M.Parallel e f) :
    (M ／ {e} ＼ {f}).Connected := by
  have h := hM.to_dual.contract_delete_connected_of_mem_triangle_of_series hT heT hfT hef (by simpa)
  rwa [h_para.parallel'.contract_delete_comm, ← connected_dual_iff, dual_contract_delete,
    ← contract_delete_comm _ (by grind)]

-- def parallelUnifOn {ι : Type*} (L : ι → Set α) (hL : Pairwise (Disjoint on L) := by grind)
-- (k : ℕ) :
--     Matroid α := (Matroid.disjointSigma (fun i ↦ unifOn (L i) 1) (by simpa)).truncateTo k

-- lemma rankTwoOn_indep_iff {ι : Type*} (L : ι → Set α) (hL) {I : Set α} {k : ℕ} :
--     (parallelUnifOn L hL k).Indep I ↔
--         I ⊆ ⋃ i, L i ∧ (∀ i, (I ∩ L i).encard ≤ 1) ∧ I.encard ≤ k := by
--   simp only [parallelUnifOn, truncateTo_indep_iff, disjointSigma_indep_iff, unifOn_ground_eq,
--     unifOn_indep_iff, Nat.cast_one, inter_subset_right, and_true]
--   tauto

-- lemma IsTriangle.small_of_isTriangle_isTriad {a b c d : α} (habc : M.IsTriangle {a, b, c})
--     (habd : M.IsTriangle {a, b, d}) (hbcd : M.IsTriad {b, c, d}) (ha : (M ／ {a}).Connected) :
--     M = parallelUnifOn #[{a}, {b, c}, {d}] := by

/-- If a four-element set `{a, b, c, d}` contains two triangles through `a` and `b`,
and a triad not containing both `a` and `b`, and `M ／ {a}` is connected,
then the matroid is `U₂,₄`, or a parallel extension of `U₂,₃`. -/
lemma IsTriangle.small_of_isTriangle_isTriad {a b c d : α} (habc : M.IsTriangle {a, b, c})
    (habd : M.IsTriangle {a, b, d}) (hbcd : M.IsTriad {b, c, d}) (ha : (M ／ {a}).Connected) :
    M ＼ {d} = unifOn {a, b, c} 2 := by
  obtain rfl | hne := eq_or_ne c d
  · simp at hbcd
  have hss : {a, b, c, d} ⊆ M.closure {a, b} := by simp [insert_subset_iff, habc.mem_closure₃,
    habd.mem_closure₃, mem_closure_of_mem', habc.mem_ground₁, habc.mem_ground₂]
  have hacl : a ∈ M.closure {b, c, d} :=
    mem_of_mem_of_subset habc.mem_closure₁ <| M.closure_subset_closure <| by grind
  have hE : M.E = {a, b, c, d}
  · have hconn := hbcd.isCircuit.eConn_add_one_eq.le
    grw [dual_dual, ← eRk_closure_eq, ← closure_insert_eq_of_mem_closure hacl,
      hss, closure_closure, eRk_closure_eq, eRk_le_encard, encard_pair_le,
      M✶.eConn_eq_eConn_delete_disjoint_add (D := {a}) (by grind), dual_dual,
      ← eConn_dual, dual_delete_dual, eLocalConn_comm,
      habc.isNonloop₁.eLocalConn_eq_one_iff.2 hacl, ← one_add_one_eq_two,
      ENat.add_one_le_add_one_iff, ENat.add_le_right_iff, or_iff_left (by simp)] at hconn
    rw [ha.eq_ground_of_eConn_eq_zero hconn (by simp) (by grind [hbcd.subset_ground]),
      contract_ground, insert_diff_self_of_mem habc.mem_ground₁]
  rw [← circuitOn_eq_unifOn, ← habc.isCircuit.restrict_eq_circuitOn, delete_eq_restrict, hE,
    show ({a, b, c, d} : Set α) \ {d} = {a, b, c} by grind]
  simp [habc.three_elements, two_add_one_eq_three]



lemma IsTriangle.triad_of_isTriangle_isTriad {a b c d : α} (habc : M.IsTriangle {a, b, c})
    (habd : M.IsTriangle {a, b, d}) (hbcd : M.IsTriad {b, c, d}) (ha : (M ／ {a}).Connected) :
    M.IsTriad {a, c, d} := by
  have h_eq := habc.small_of_isTriangle_isTriad habd hbcd ha
  rw [← dual_inj, dual_delete, unifOn_dual_eq' (j := 1) (by grind [habc.three_elements])] at h_eq
  have hC : (M✶ ／ {d}).IsCircuit {a, c} := by grind [unifOn_isCircuit_iff, encard_pair habc.ne₁₃]
  obtain ⟨T, hT, hacT, hTss⟩ := hC.exists_subset_isCircuit_of_contract
  simp only [union_singleton] at hTss
  by_cases hd : d ∈ T
  · rwa [isTriad_iff, encard_insert_of_notMem (by grind), encard_pair hbcd.ne₂₃,
      ← show T = {a, c, d} by grind, and_iff_left (by grind)]
  rw [show T = {a, c} by grind] at hT
  have hwin := habd.reverse.mem_iff_mem_of_isCocircuit hT
  grind
  -- have := IsCircuit.exists_subset_isCircuit_of_contract
