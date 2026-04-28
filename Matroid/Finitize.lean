import Matroid.Rank.Skew

variable {α ι : Type*} {M : Matroid α} {A B C X Y I J : Set α} {e f : α} {k : ℕ∞}
  {μ : Matroid α → Set α → ℕ∞}

-- set_option linter.style.longLine false

open Set Function

namespace Matroid

@[mk_iff]
structure StronglyPreservable (μ : Matroid α → Set α → ℕ∞) : Prop where
  dual : ∀ (M : Matroid α) X, μ M✶ X = μ M X
  inter_ground : ∀ M X, μ M (X ∩ M.E) = μ M X
  delete_le : ∀ (M : Matroid α) X D, μ (M ＼ D) X ≤ μ M X
  base_preservable : ∀ ⦃M B X k⦄, M.IsBase B → k ≤ μ M X → ∃ V ⊆ M.E, Disjoint V B ∧ V.encard ≤ k ∧
    μ (M ↾ (B ∪ V)) X = k

lemma StronglyPreservable.contract_le {μ} (hμ : StronglyPreservable μ) (M : Matroid α) X C :
    μ (M ／ C) X ≤ μ M X := by
  grw [← hμ.dual, dual_contract, hμ.delete_le, hμ.dual]

lemma StronglyPreservable.le_of_isMinor {μ} (hμ : StronglyPreservable μ) {M N : Matroid α}
    (h : N ≤m M) (X : Set α) : μ N X ≤ μ M X := by
  obtain ⟨C, D, rfl⟩ := h
  grw [hμ.delete_le, hμ.contract_le]

lemma StronglyPreservable.exists_preserve_eq {μ} (hμ : StronglyPreservable μ) (hB : M.IsBase B)
    (hk : k ≤ μ M X) : ∃ U V, U ⊆ B ∧ V ⊆ M.E ∧ Disjoint V B ∧ U.encard ≤ k ∧ V.encard ≤ k ∧
    μ (M ／ (B \ U) ＼ ((M.E \ B) \ V)) X = k := by
  obtain ⟨V, hVE, hVB, hVcard, hVconn⟩ := hμ.base_preservable hB hk
  have hB' : (M ↾ (B ∪ V)).IsBase B := IsBasis.isBase_restrict <|
    hB.isBasis_ground.isBasis_subset subset_union_left (union_subset hB.subset_ground hVE)
  have h' := hμ.base_preservable hB'.compl_isBase_dual (X := X) (k := k)
  rw [hμ.dual, hVconn, imp_iff_right rfl.le] at h'
  obtain ⟨U, hUE, hUdj, hUcard, hUconn⟩ := h'
  simp only [restrict_ground_eq, union_diff_left, hVB.sdiff_eq_left] at hUdj
  rw [dual_ground, restrict_ground_eq, union_comm, ← diff_subset_iff, hUdj.sdiff_eq_left] at hUE
  refine ⟨U, V, hUE, hVE, hVB, hUcard, hVcard, ?_⟩
  rw [← hUconn, ← hμ.dual, restrict_ground_eq, union_diff_cancel_left (by grind), dual_delete,
    dual_contract, ← contract_delete_comm _ (by grind), delete_eq_restrict, contract_ground,
    dual_ground, diff_diff, diff_diff_cancel_left (by grind [hB.subset_ground]),
    ← dual_delete, delete_compl, union_diff_distrib, diff_diff_cancel_left hUE,
    (hVB.mono_right diff_subset).sdiff_eq_left, union_comm U]

lemma StronglyPreservable.exists_preserve_le {μ} (hμ : StronglyPreservable μ)
    (hB : M.IsBase B) (hk : k ≤ μ M X) :
    ∃ U V, U ⊆ B ∧ V ⊆ M.E ∧ Disjoint V B ∧ U.encard ≤ k ∧ V.encard ≤ k
      ∧ ∀ C ⊆ B, ∀ D ⊆ M.E \ B, Disjoint C U → Disjoint D V →
      k ≤ μ (M ／ C ＼ D) X := by
  obtain ⟨U, V, hUB, hVE, hVB, hUk, hVk, h⟩ := hμ.exists_preserve_eq hB hk
  refine ⟨U, V, hUB, hVE, hVB, hUk, hVk, fun C hC D hD hCU hDV ↦ ?_⟩
  rw [← h]
  refine hμ.le_of_isMinor ?_ X
  refine (contract_isMinor_of_subset _ (by grind)).delete_isMinor_delete_of_subset (by grind) ?_
  grind [contract_ground]

lemma StronglyPreservable.exists_finite_counterexample_of_lt_sum {ι : Type*} [Fintype ι] {μ}
    (hμ : StronglyPreservable μ) (M : Matroid α) (g : Matroid α → ℕ∞) (hg : Monotone g)
    (X : ι → Set α) (h_lt : g M < ∑ i, μ M (X i)) :
    ∃ N, N ≤m M ∧ N.Finite ∧ g N < ∑ i, μ N (X i) := by
  obtain ⟨B, hB⟩ := M.exists_isBase
  obtain ⟨s, hs⟩ | hfinY := exists_or_forall_not (fun i ↦ μ M (X i) = ⊤)
  · obtain ⟨U, V, hUV, hE, hVB, hUcard, hVcard, hconn⟩ :=
      hμ.exists_preserve_eq (k := g M + 1) (X := X s) hB (by simp [hs])
    set N := M ／ (B \ U) ＼ ((M.E \ B) \ V) with hN_def
    have hNM : N ≤ M := contract_delete_isMinor ..
    have hNE : N.E = U ∪ V := by
      rw [hN_def, delete_ground, contract_ground]
      have := hB.subset_ground
      tauto_set
    refine ⟨N, hNM, ?_, ?_⟩
    · grw [finite_iff, hNE, finite_union, ← encard_lt_top_iff, ← encard_lt_top_iff, hUcard, hVcard]
      simpa using h_lt.trans_le le_top
    grw [hg hNM, ← Finset.single_le_sum_of_canonicallyOrdered (f := fun i ↦ μ N (X i))
      (Finset.mem_univ s), hconn]
    simp [(h_lt.trans_le le_top).ne]
  simp_rw [← lt_top_iff_ne_top] at hfinY
  choose U V hYUB hYVE hYVdj hUYcard hVYcard hVY
    using fun i ↦ hμ.exists_preserve_le hB (X := X i) rfl.le
  set P := ⋃ i, U i with hP
  set Q := ⋃ i, V i with hQ
  have hPfin : P.Finite := by
    refine finite_univ.iUnion (fun i _ ↦ ?_) <| by simp
    grw [← encard_lt_top_iff, hUYcard]
    exact hfinY i
  have hQfin : Q.Finite := by
    refine finite_univ.iUnion (fun i _ ↦ ?_) <| by simp
    grw [← encard_lt_top_iff, hVYcard]
    exact hfinY i
  set N := M ／ (B \ P) ＼ ((M.E \ B) \ Q) with hN
  have hNM : N ≤m M := contract_delete_isMinor ..
  refine ⟨N, hNM, ⟨(hPfin.union hQfin).subset ?_⟩, ?_⟩
  · rw [hN, delete_ground, contract_ground]
    tauto_set
  grw [hg hNM]
  refine h_lt.trans_le <| Finset.sum_le_sum fun i _ ↦ hVY _ _ diff_subset _ diff_subset ?_ ?_ <;>
  exact disjoint_sdiff_left.mono_right <| subset_iUnion ..

lemma StronglyPreservable.exists_finite_counterexample_of_sum_lt_sum (hμ : StronglyPreservable μ)
    {ι η : Type*} [Fintype ι] [Fintype η]
    (M : Matroid α) (X : ι → Set α) (Y : η → Set α)
    (h_lt : ∑ i, μ M (X i) < ∑ i, μ M (Y i)) :
    ∃ N, N ≤m M ∧ N.Finite ∧ ∑ i, μ N (X i) < ∑ i, μ N (Y i) :=
  hμ.exists_finite_counterexample_of_lt_sum _ (fun M ↦ ∑ i, μ M (X i))
    (fun _ _ hNM ↦ Finset.sum_le_sum fun _ _ ↦ hμ.le_of_isMinor hNM _) _ h_lt

end Matroid
