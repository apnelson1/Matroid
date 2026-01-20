import Matroid.Connectivity.Separation.Internal

variable {α : Type*} {M N : Matroid α} {j k : ℕ∞} {d k : ℕ∞} {A X Y : Set α} {P : M.Separation}
  {b : Bool}

open Set Matroid Matroid.Separation Function

lemma Monotone.indicator_monotone {α β : Type*} [Preorder α] [Preorder β] [Zero β] {f : α → β}
    {s : Set α} (hf : Monotone f) (hle : 0 ≤ f) (hs : ∀ ⦃x y⦄, x ∈ s → x ≤ y → y ∈ s) :
    Monotone (s.indicator f) := by
  intro x y hxy
  by_cases hx : x ∈ s
  · simp [hx, hs hx hxy, hf hxy]
  by_cases hy : y ∈ s
  · simp only [hx, not_false_eq_true, indicator_of_notMem, hy, indicator_of_mem]
    apply hle
  simp [hx, hy]

namespace Matroid.Separation

/-- A separation `P` of `N` splits in a matroid `M` if one side of `P` has a partition into two
sets with connectivity in `M` not exceeding the connectivity of `P` in `N`.
TODO : Can we state this definition for infinite matroids without comparing numbers? -/
def SplitsIn (P : N.Separation) (M : Matroid α) : Prop :=
    ∃ (i : Bool) (P₀ : (P i).Bipartition), ∀ j, M.eConn (P₀ j) ≤ P.eConn

lemma splitsIn_self (P : M.Separation) : P.SplitsIn M :=
  ⟨true, Bipartition.single _ true, by simp [Bipartition.single_apply (P true)]⟩

end Separation

/-- `N` adheres to `M` if every separation of `N` splits in `M`.
Usually `N` is a minor of `M` in applications, but we only require that `N.E ⊆ M.E`. -/
@[mk_iff]
structure AdheresTo (N M : Matroid α) : Prop where
  subset : N.E ⊆ M.E
  forall_splits : ∀ (P : N.Separation), P.SplitsIn M

lemma adheresTo_iff_of_subset (hNM : N.E ⊆ M.E) :
    N.AdheresTo M ↔ ∀ (P : N.Separation), P.SplitsIn M := by
  simp [adheresTo_iff, hNM]

lemma adheresTo_self (M : Matroid α) : M.AdheresTo M :=
  ⟨rfl.subset, fun P ↦ P.splitsIn_self⟩

private lemma num_aux {a b c d m n : ℕ∞} (h1 : n < max a b) (h2 : n < max c d) (h3 : m < max a c)
    (h4 : m < max b d) (h5 : a + d ≤ m + n + 1) (h6 : b + c ≤ m + n + 1) : False := by
  enat_to_nat
  simp only [lt_sup_iff, Nat.cast_lt] at h1 h2 h3 h4
  grind

/-- For every element of a matroid `M`, either `M ／ e` or `M ＼ e` adheres to `M`.
The proof is an easy application of the Bixby-Coullard inequality. -/
lemma adheresTo_contract_or_delete (M : Matroid α) (e : α) :
    (M ／ {e}).AdheresTo M ∨ (M ＼ {e}).AdheresTo M := by
  wlog he : e ∈ M.E with aux
  · simp [contractElem_eq_self he, M.adheresTo_self]
  rw [adheresTo_iff_of_subset diff_subset, adheresTo_iff_of_subset diff_subset]
  simp only [SplitsIn]
  by_contra! hcon
  obtain ⟨⟨P, hP⟩, Q, hQ⟩ := hcon
  replace hP : ∀ i, ∃ j, P.eConn < M.eConn (P i ∩ Q j) :=
    by simpa [Set.inter_comm] using fun i ↦ hP i <| Q.toBipartition.induce P.subset
  replace hQ : ∀ i, ∃ j, Q.eConn < M.eConn (P j ∩ Q i) :=
    by simpa using fun i ↦ hQ i <| P.toBipartition.induce Q.subset
  simp_rw [Bool.forall_bool, Bool.exists_bool] at hP hQ
  have h1 := P.eConn_inter_add_eConn_inter_le_add_of_singleton Q.symm true
  have h2 := P.eConn_inter_add_eConn_inter_le_add_of_singleton Q false
  simp only [Separation.symm_apply, Bool.not_true, Bool.not_false, eConn_symm] at h1 h2
  simp_rw [← lt_max_iff] at hP hQ
  exact num_aux hQ.1 hQ.2 hP.1 hP.2 h2 h1

lemma AdheresTo.seqConnected_add_two_mul {f : ℕ∞ → ℕ∞} (hNM : N.AdheresTo M) (hf : Monotone f)
    (hM : M.SeqConnected Matroid.tutteWeight f) :
    N.SeqConnected Matroid.tutteWeight (fun i ↦ i + 2 * f i) := by
  rw [seqConnected_tutteWeight_iff (by simp)]
  simp_rw [← add_assoc, ← two_mul, ← mul_add]
  intro P
  obtain ⟨i, P₀, hP₀⟩ := hNM.forall_splits P
  have aux := fun j : Bool ↦ hM.exists_encard_le (M.ofSetSep (P₀ j) true
    ((P₀.subset.trans P.subset).trans hNM.subset))
  simp only [eConn_ofSetSep,  Bool.exists_bool, ofSetSep_true_false, ofSetSep_apply_self] at aux
  obtain ⟨j, hj⟩ | h :=
    exists_or_forall_not (fun j ↦ (M.E \ P₀ j).encard ≤ M.eConn (P₀ j) + f (M.eConn (P₀ j)))
  · use !i
    grw [← hf (hP₀ j), ← hP₀, ← hj, two_mul, ← le_add_self, ← P.compl_eq]
    exact encard_le_encard (diff_subset_diff hNM.subset P₀.subset)
  simp_rw [or_iff_right (h _)] at aux
  refine ⟨i, ?_⟩
  grw [← P₀.union_eq, encard_union_eq P₀.disjoint_true_false, aux, hf (hP₀ _), aux, hf (hP₀ _),
    hP₀, hP₀, two_mul]

lemma AdheresTo.connected_of_connected [N.Nonempty] (hNM : N.AdheresTo M) (hM : M.Connected) :
    N.Connected := by
  have _ : M.Nonempty := (ground_nonempty_iff _).1 <| N.ground_nonempty.mono hNM.subset
  rw [← tutteConnected_two_iff, ← one_add_one_eq_two, tutteConnected_iff_seqConnected'] at hM ⊢
  refine (hNM.seqConnected_add_two_mul ?_ hM).mono fun n k ↦ ?_
  · refine monotone_const.indicator_monotone (fun _ ↦ le_top) fun x y hx hxy ↦ ?_
    grw [mem_setOf, ← hxy]
    assumption
  obtain rfl | ⟨k, rfl⟩ := k.eq_zero_or_exists_eq_add_one <;> simp

lemma AdheresTo.internallyConnected_of_tutteConnected_three (hNM : N.AdheresTo M)
    (hM : M.TutteConnected 3) : N.InternallyConnected 3 := by
  rw [show (3 : ℕ∞) = 1 + 1 + 1 from rfl] at *
  simp only [tutteConnected_iff_seqConnected', ENat.add_lt_add_right_iff, ne_eq,
    ENat.one_ne_top, not_false_eq_true, and_true] at hM
  refine (hNM.seqConnected_add_two_mul ?_ hM).mono_right fun n ↦ ?_
  · exact monotone_const.indicator_monotone (fun _ ↦ le_top) fun _ _ hx ↦ lt_of_lt_of_le hx
  obtain rfl | hne := eq_or_ne n ⊤
  · simp
  obtain hle | hlt := le_or_gt n 1
  · obtain rfl | rfl := ENat.le_one_iff_eq_zero_or_eq_one.1 hle <;> simp
  simp [indicator_apply, hne, hlt]

lemma Connected.contract_or_delete_connected {e : α} (hM : M.Connected) (hnt : M.E.Nontrivial) :
    (M ／ {e}).Connected ∨ (M ＼ {e}).Connected := by
  have _ : (M ／ {e}).Nonempty := ⟨hnt.diff_singleton_nonempty e⟩
  have _ : (M ＼ {e}).Nonempty := ⟨hnt.diff_singleton_nonempty e⟩
  exact (M.adheresTo_contract_or_delete e).elim
    (.inl ∘ fun h ↦ h.connected_of_connected hM) (.inr ∘ fun h ↦ h.connected_of_connected hM)

lemma TutteConnected.contract_or_delete_internallyConnected_three
    (hM : M.TutteConnected 3) {e : α} :
    (M ／ {e}).InternallyConnected 3 ∨ (M ＼ {e}).InternallyConnected 3 :=
  (M.adheresTo_contract_or_delete e).elim
    (.inl ∘ fun h ↦ h.internallyConnected_of_tutteConnected_three hM)
    (.inr ∘ fun h ↦ h.internallyConnected_of_tutteConnected_three hM)


-- lemma TutteConnected.exists_contract_verticallyConnected_three [M.RankFinite]
--     (h : M.TutteConnected 3) : ∃ e ∈ M.E, (M ／ {e}).VerticallyConnected 3 := sorry

-- lemma VerticallyConnected.exists_contract_verticallyConnected_three [M.RankFinite]
--     (h : M.VerticallyConnected 3) : ∃ e ∈ M.E, (M ／ {e}).VerticallyConnected 3 := by
--   obtain ⟨N, hN⟩ := M.exists_isSimplification
--   have := hN.isRestriction.rankFinite
--   obtain ⟨e, he, hMe⟩ :=
--     (hN.tutteConnected_of_verticallyConnected_three h).exists_contract_verticallyConnected_three
--   exact ⟨e, hN.isRestriction.subset he,
--     (hN.simplifies.contract (by simpa)).verticallyConnected_iff.1 hMe⟩






end Matroid
