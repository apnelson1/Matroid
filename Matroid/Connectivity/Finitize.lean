import Matroid.Connectivity.Local

variable {α : Type*} {M : Matroid α} {A B C X Y : Set α} {e f : α}

open Set

namespace Matroid

lemma exists_big_skew (hB : M.IsBase B) (hX : X ⊆ M.E := by aesop_mat) :
    ∃ I ⊆ B, I.encard = M.eRk X ∧ M.Skew (B \ I) X := by
  obtain ⟨IX, hIX⟩ := M.exists_isBasis X
  obtain ⟨B', hB', hIXB', hB'IX⟩ :=  hIX.indep.exists_isBase_subset_union_isBase hB
  refine ⟨B \ (B' \ IX), diff_subset, ?_, ?_⟩
  · rw [hIX.eRk_eq_encard, diff_diff_right,
      encard_union_eq (disjoint_sdiff_left.mono_right (inter_subset_right.trans hIXB')),
      hB.encard_diff_comm hB', ← encard_union_eq (disjoint_sdiff_left.mono_right inter_subset_left)]
    congr
    tauto_set
  rw [diff_diff_right, skew_iff_closure_skew_right, ← hIX.closure_eq_closure,
    ← skew_iff_closure_skew_right]
  simp only [sdiff_self, bot_eq_empty, empty_union]
  exact (hB'.indep.subset_skew_diff hIXB').symm.mono_left inter_subset_right

lemma eLocalConn_keep (hB : M.IsBase B) (X Y : Set α) :
    ∃ I ⊆ B, I.encard ≤ M.eLocalConn X Y ∧
    ∀ J ⊆ B, Disjoint J I → (M ／ J).eLocalConn X Y = M.eLocalConn X Y := by
  wlog h_ind : M.Indep X ∧ M.Indep Y generalizing X Y with aux
  · obtain ⟨IX, hIX⟩ := M.exists_isBasis' X
    obtain ⟨IY, hIY⟩ := M.exists_isBasis' Y
    simp_rw [← M.eLocalConn_closure_closure X Y, ← hIX.closure_eq_closure, ← hIY.closure_eq_closure,
      ← (M ／ _).eLocalConn_closure_closure X Y, contract_closure_eq,
      ← closure_union_congr_left hIX.closure_eq_closure,
      ← closure_union_congr_left hIY.closure_eq_closure, ← contract_closure_eq,
      eLocalConn_closure_closure]
    exact aux _ _ ⟨hIX.indep, hIY.indep⟩
  obtain ⟨hX, hY⟩ := h_ind
  obtain ⟨K, hK, hXK⟩ := hX.subset_isBasis_of_subset (show X ⊆ X ∪ Y from subset_union_left)

  sorry

lemma foo {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] (S₁ : ι₁ → Set α) (S₂ : ι₂ → Set α)
    (h_lt : ∑ i, M.eRk (S₁ i) < ∑ i, M.eRk (S₂ i)) :
    ∃ (N : Matroid α), (∀ i, (S₁ i ∩ N.E).Finite) ∧ (∀ i, (S₂ i ∩ N.E).Finite)
      ∧ ∑ i, N.eRk (S₁ i) < ∑ i, N.eRk (S₂ i) := by
  obtain (⟨i, hi⟩ | forall_fin) := exists_or_forall_not (fun i ↦ M.eRk (S₂ i) = ⊤)
  · obtain ⟨I, hI⟩ := M.exists_isBasis' (S₂ i)
    rw [hI.eRk_eq_encard, encard_eq_top_iff] at hi
    obtain ⟨I₀, hI₀, hlt', hfin⟩ := hi.exists_finite_subset_encard_gt' (h_lt.trans_le le_top).ne
    refine ⟨M ↾ I₀, fun _ ↦ hfin.inter_of_right _, fun _ ↦ hfin.inter_of_right _, ?_⟩
    simp only [restrict_eRk_eq']
    grw [Finset.sum_le_sum (fun i _ ↦ M.eRk_mono inter_subset_left),
      ← Finset.single_le_sum (a := i) (by simp) (by simp),
      inter_eq_self_of_subset_right (hI₀.trans hI.subset), (hI.indep.subset hI₀).eRk_eq_encard]
    assumption
  simp only [eRk_eq_top_iff, not_not] at forall_fin
  sorry
    -- have hfin := h_lt.trans_le <| le_top (a := ∑ i, M.eRk (S₂ i))
    -- -- have h_lt := hi ▸ (h_lt.trans_le <| le_top (a := ∑ i, M.eRk (S₂ i)))
    -- grw [← ENat.add_one_le_iff (by intro h; simp [h] at h_lt),
    --   le_top (a := ∑ i, M.eRk (S₂ i)), hi.encard_eq] at h_lt


    -- obtain ⟨J, hJI, ⟩ := exists_subset_encard_eq ()


    -- have h' : B' \ B = IX \ B := by
    --   tauto_set
    -- nth_rw 2 [← diff_union_inter IX B
