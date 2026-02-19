import Matroid.Connectivity.Basic

variable {α ι : Type*} {M : Matroid α} {A B C X Y I J : Set α} {e f : α} {k : ℕ∞}

set_option linter.style.longLine false

open Set Function

namespace Matroid

lemma IsBase.exists_preserve_eConn_delete (hB : M.IsBase B) (hk : k ≤ M.eConn X) :
    ∃ V ⊆ M.E, Disjoint V B ∧ V.encard = k ∧ (M ＼ ((M.E \ B) \ V)).eConn X = k := by
  have h1 := hB.exists_restrict_multiConn_eq'
      (X := fun b ↦ bif b then X ∩ M.E else M.E \ X) (k := k)
  simp only [inter_comm X, pairwise_disjoint_on_bool, disjoint_sdiff_inter.symm, iUnion_bool,
    cond_true, cond_false, inter_union_diff, ← eLocalConn_eq_multiConn, forall_const] at h1
  rw [inter_comm, ← eConn_eq_eLocalConn', imp_iff_right hk] at h1
  obtain ⟨R, hRE, hBR, hRK, hconnk⟩ := h1
  refine ⟨R \ B, diff_subset.trans hRE, disjoint_sdiff_left, hRK, ?_⟩
  have hrw1 : X ∩ M.E ∩ R = X ∩ (M ↾ R).E := by
    simp [inter_assoc, inter_eq_self_of_subset_right hRE]
  have hrw2 : M.E \ X ∩ R = (M ↾ R).E \ X := by
    rw [restrict_ground_eq, ← inter_diff_right_comm, inter_eq_self_of_subset_right hRE]
  simp_rw [Bool.apply_cond (f := fun X ↦ X ∩ R), hrw1, hrw2, ← eLocalConn_eq_multiConn,
    ← eConn_eq_eLocalConn'] at hconnk
  rwa [diff_diff_right, disjoint_sdiff_left.inter_eq, union_empty, diff_diff, delete_compl,
    union_eq_self_of_subset_left hBR]

lemma IsBase.exists_preserve_eConn_delete_contract (hB : M.IsBase B) (hk : k ≤ M.eConn X) :
    ∃ U V, U ⊆ B ∧ V ⊆ M.E ∧ Disjoint V B ∧ U.encard = k ∧ V.encard = k ∧
    (M ／ (B \ U) ＼ ((M.E \ B) \ V)).eConn X = k := by
  obtain ⟨V, hVE, hVB, hVcard, hVconn⟩ := hB.exists_preserve_eConn_delete hk
  have hB' : (M ＼ ((M.E \ B) \ V)).IsBase B := by
    rw [delete_isBase_iff, diff_diff_right, diff_diff_cancel_left hB.subset_ground]
    exact hB.isBasis_of_subset (union_subset hB.subset_ground inter_subset_left) subset_union_left
  have h' := hB'.compl_isBase_dual.exists_preserve_eConn_delete (X := X) (k := k)
  rw [eConn_dual, hVconn, imp_iff_right rfl.le] at h'
  obtain ⟨U, hUE, Udj, hUcard, hUconn⟩ := h'
  have hrw : (M ＼ ((M.E \ B) \ V))✶.E = B ∪ V := by
    rw [dual_ground, delete_ground, diff_diff_right, diff_diff_cancel_left hB.subset_ground,
      inter_eq_self_of_subset_right hVE]
  simp only [dual_delete, contract_ground, dual_ground, diff_diff_right, sdiff_sdiff_right_self,
    inf_eq_inter, inter_eq_self_of_subset_right hB.subset_ground, inter_eq_self_of_subset_right hVE,
    delete_ground, union_diff_left, union_diff_right,
    inter_eq_self_of_subset_right subset_union_left, union_eq_self_of_subset_left diff_subset]
    at hUconn
  simp only [delete_ground, diff_diff_right, sdiff_sdiff_right_self, inf_eq_inter,
    inter_eq_self_of_subset_right hB.subset_ground, inter_eq_self_of_subset_right hVE,
    union_diff_left, hVB.sdiff_eq_left] at Udj
  rw [hrw, union_comm,  ← diff_subset_iff, Udj.sdiff_eq_left] at hUE
  refine ⟨U, V, hUE, hVE, hVB, hUcard, hVcard, ?_⟩
  rwa [← dual_delete_contract, eConn_dual, ← contract_delete_comm] at hUconn
  tauto_set

lemma IsBase.exists_preserve_eConn_delete_of_le (hB : M.IsBase B) (hk : k ≤ M.eConn X) :
    ∃ V ⊆ M.E, Disjoint V B ∧ V.encard = k ∧ ∀ D ⊆ M.E \ B, Disjoint D V → k ≤ (M ＼ D).eConn X := by
  obtain ⟨V, hVE, hVB, hVcard, hCconn⟩ := hB.exists_preserve_eConn_delete hk
  refine ⟨V, hVE, hVB, hVcard, fun D hD hDV ↦ ?_⟩
  grw [← hCconn]
  exact (delete_isRestriction_of_subset _ (subset_diff.2 ⟨hD, hDV⟩)).isMinor.eConn_le _

lemma IsBase.exists_preserve_eConn_contract_delete_of_le (hB : M.IsBase B) (hk : k ≤ M.eConn X) :
    ∃ U V, U ⊆ B ∧ V ⊆ M.E ∧ Disjoint V B ∧ U.encard = k ∧ V.encard = k
      ∧ ∀ C ⊆ B, ∀ D ⊆ M.E \ B, Disjoint C U → Disjoint D V → k ≤ (M ／ C ＼ D).eConn X := by
  obtain ⟨U, V, hUB, hVE, hVB, hUcard, hVcard, hconn⟩ := hB.exists_preserve_eConn_delete_contract hk
  refine ⟨U, V, hUB, hVE, hVB, hUcard, hVcard, fun C hC D hD hCU hDV ↦ ?_⟩
  rw [← hconn]
  refine IsMinor.eConn_le ?_ _
  have hDss : D ⊆ (M.E \ B) \ V := subset_diff.2 ⟨hD, hDV⟩
  refine (delete_isRestriction_of_subset _ hDss).isMinor.trans (IsMinor.delete_isMinor_delete ?_ ?_)
  · exact contract_isMinor_of_subset _ (subset_diff.2 ⟨hC, hCU⟩)
  grw [hD, contract_ground, diff_subset_diff_right diff_subset]

/-- If an inequality of the form `∑ i, M.eConn (X i) ≤ g M` for some minor-monotone function `g`
fails for some matroid, then it fails for a finite matroid.
Can be used to reduce harder proofs for infinite matroids to numerical calculations where
they work in the finite case.
TODO : Allow the RHS to involve rank and nullity terms. -/
lemma exists_finite_counterexample_of_lt_sum_eConn {ι : Type*} [Fintype ι]
    (M : Matroid α) (g : Matroid α → ℕ∞) (hg : Monotone g) (X : ι → Set α)
    (h_lt : g M < ∑ i, M.eConn (X i)) : ∃ N, N ≤m M ∧ N.Finite ∧ g N < ∑ i, N.eConn (X i) := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  obtain ⟨s, hs⟩ | hfinY := exists_or_forall_not (fun i ↦ M.eConn (X i) = ⊤)
  · obtain ⟨U, V, hUV, hE, hVB, hUcard, hVcard, hconn⟩ :=
      hB.exists_preserve_eConn_delete_contract (k := g M + 1) (X := X s) (by simp [hs])
    set N := M ／ (B \ U) ＼ ((M.E \ B) \ V) with hN_def
    have hNM : N ≤ M := contract_delete_isMinor ..
    have hNE : N.E = U ∪ V := by
      rw [hN_def, delete_ground, contract_ground]
      have := hB.subset_ground
      tauto_set
    refine ⟨N, hNM, ?_, ?_⟩
    · rw [finite_iff, hNE, finite_union, ← encard_lt_top_iff, ← encard_lt_top_iff, hUcard, hVcard]
      simpa using h_lt.trans_le le_top
    grw [hg hNM, ← Finset.single_le_sum_of_canonicallyOrdered (f := fun i ↦ N.eConn (X i))
      (Finset.mem_univ s), hconn]
    simp [(h_lt.trans_le le_top).ne]
  simp_rw [← lt_top_iff_ne_top] at hfinY
  choose U V hYUB hYVE hYVdj hUYcard hVYcard hVY
    using fun i ↦ hB.exists_preserve_eConn_contract_delete_of_le (X := X i) rfl.le
  set P := ⋃ i, U i with hP
  set Q := ⋃ i, V i with hQ
  have hPfin : P.Finite := by
    refine finite_univ.iUnion (fun i _ ↦ ?_) <| by simp
    rw [← encard_lt_top_iff, hUYcard]
    exact hfinY i
  have hQfin : Q.Finite := by
    refine finite_univ.iUnion (fun i _ ↦ ?_) <| by simp
    rw [← encard_lt_top_iff, hVYcard]
    exact hfinY i
  set N := M ／ (B \ P) ＼ ((M.E \ B) \ Q) with hN
  have hNM : N ≤m M := contract_delete_isMinor ..
  refine ⟨N, hNM, ⟨(hPfin.union hQfin).subset ?_⟩, ?_⟩
  · rw [hN, delete_ground, contract_ground]
    tauto_set
  grw [hg hNM]
  refine h_lt.trans_le <| Finset.sum_le_sum fun i _ ↦ hVY _ _ diff_subset _ diff_subset ?_ ?_ <;>
  exact disjoint_sdiff_left.mono_right <| subset_iUnion ..

/-- If an inequality involving sums of connectivites fails for some matroid,
then it will also fail in some finite minor.
This allows one to reduce inequalities that need intricate proofs to the rank calculations
that work in the finite case.  -/
lemma exists_finite_counterexample_of_sum_eConn_lt_sum_eConn {ι η : Type*} [Fintype ι] [Fintype η]
    (M : Matroid α) (X : ι → Set α) (Y : η → Set α)
    (h_lt : ∑ i, M.eConn (X i) < ∑ i, M.eConn (Y i)) :
    ∃ N, N ≤m M ∧ N.Finite ∧ ∑ i, N.eConn (X i) < ∑ i, N.eConn (Y i) :=
  exists_finite_counterexample_of_lt_sum_eConn _ (fun M ↦ ∑ i, M.eConn (X i))
    (fun _ _ hNM ↦ Finset.sum_le_sum fun _ _ ↦ IsMinor.eConn_le hNM _) _ h_lt

end Matroid
