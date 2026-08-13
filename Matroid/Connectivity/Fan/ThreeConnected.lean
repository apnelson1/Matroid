import Matroid.Connectivity.Fan.Cyclic
import Matroid.Connectivity.Separation.Tutte
import Matroid.Connectivity.Splitter.TutteTriangle

open Set List

namespace Matroid

variable {α β : Type*} {F : List α} {b c d : Bool} {M : Matroid α}

/-- If `F` is a fan in a `3`-connected matroid that is not cyclic (starting with a joint, say),
and deleting the first element destroys `3`-connectivity, then the first element is in a triad
containing at least one other element of the fan. -/
lemma IsFan.exists_triad_of_not_tutteConnected_three_remove (h : M.IsFan F b c) (h4 : 4 ≤ F.length)
    (hM : M.TutteConnected 3) (hnf : ¬ M.IsCyclicFan F b)
    (ht : ¬ (M.remove b {F[0]}).TutteConnected 3) :
    ∃ (i : ℕ) (hi : i ≤ 1), (∃ x ∉ F, (M.bDual !b).IsTriangle {x, F[0], F[i + 1]})
      ∨ ∃ (j : ℕ) (hij : i + 1 < j) (hj : j < F.length),
      (M.bDual !b).IsTriangle {F[0], F[i + 1], F[j]} := by
  wlog hb : b = false generalizing M b c with aux
  · exact Exists.imp (by simp) <| aux h.dual hM.dual (by simpa) (by simpa [← remove_dual])
      (by grind)
  subst hb
  have hM4 : 4 ≤ M.E.encard := by
    grw [← h.subset_ground, h.nodup.encard_toSet_eq, ← h4, Nat.cast_ofNat]
  obtain hM4_eq | hM5 := hM4.eq_or_lt
  · obtain ⟨-, h⟩ := h.isCyclicFan_of_ground_eq (hM.simple hM4) (hM.dual.simple (by simpa))
      (Finite.eq_of_subset_of_encard_le (by simp) h.subset_ground
        (by grw [← hM4_eq, h.nodup.encard_toSet_eq, ← h4, Nat.cast_ofNat]))
    contradiction
  have aux {x} : 4 ≤ (M.E \ {x}).encard := by
    grw [← ENat.add_one_le_add_one_iff, ← encard_le_encard_sdiff_singleton_add_one,
      Order.add_one_le_of_lt hM5]
  have hF1 : ¬ (M ＼ {F[1]}).TutteConnected 3 := by
    intro hF1
    have hsi : (M✶ ／ {F[1]}).Simple := by simpa using hF1.dual.simple (by simpa using aux)
    have hwin := (h.isTriad_getElem_of_eq 1 rfl).parallel_contract₁.eq
    simp [h.nodup.getElem_inj_iff] at hwin
  obtain ⟨K, hK, h0K, h12K⟩ := tutte_triangle hM (h.isTriangle_bDual (by lia)) hM4 ht hF1
  obtain ⟨i, hi, hiK, himin⟩ :
    ∃ (i : ℕ) (hi : i ≤ 1), F[i + 1] ∈ K ∧ ∀ j (hj : j < i), F[j + 1] ∉ K := by
    exact h12K.elim (fun h ↦ ⟨0, by lia, by grind⟩) (fun h ↦ ⟨1, by lia, by grind⟩)
  refine ⟨i, hi, ?_⟩
  obtain ⟨z, hz0, hzi, rfl⟩ :=
    exists_eq_of_encard_eq_three_of_mem_of_mem hK.three_elements h0K hiK
    (by simp [h.nodup.getElem_inj_iff])
  by_cases hz : z ∈ F
  · obtain ⟨j, hjlt, rfl⟩ := getElem_of_mem hz
    exact .inr ⟨j, by grind, hjlt, hK⟩
  exact .inl ⟨z, hz, hK.rotate⟩

lemma IsFan.exists_extend_of_not_tutteConnected_remove₄ (h : M.IsFan F b c) (h4 : F.length = 4)
    (hM : M.TutteConnected 3) (hnf : ¬ M.IsCyclicFan F b)
    (ht : ¬ (M.remove b {F[0]}).TutteConnected 3) :
    ∃ x, M.IsFan (x :: F) (!b) c ∨ M.IsFan [x, F[0], F[2], F[1], F[3]] (!b) c := by
  have hM4 : 4 ≤ M.E.encard := by
    grw [← h.subset_ground, h.nodup.encard_toSet_eq, h4, Nat.cast_ofNat]
  obtain rfl : c = !b := by simpa [h4] using h.bool_right_eq
  by_cases h0 : F[0] ∈ (M.bDual (!b)).closure {x | x ∈ F.tail}
  · exact False.elim <| hnf <| h.isCyclicFan_of_tutteConnected_three_of_mem_closure hM hM4 h0
  obtain ⟨i, hi, ⟨x, hxF, hT⟩ | ⟨j, hij, hj, hT⟩⟩ :=
    h.exists_triad_of_not_tutteConnected_three_remove h4.ge hM hnf ht
  · obtain rfl | rfl := Nat.le_one_iff_eq_zero_or_eq_one.1 hi
    · exact ⟨x, .inl <| h.cons' hxF <| by simpa [head_eq_getElem]⟩
    exact ⟨x, .inr <| (h.swap_middle h4).cons' (by grind [mem_iff_getElem]) (by simpa using hT)⟩
  refine False.elim <| h0 <| mem_of_mem_of_subset hT.mem_closure₁ <| closure_subset_closure _ ?_
  simp [insert_subset_iff, getElem_mem_tail, show j ≠ 0 by lia]

/-- If deleting a joint a the beginning of a noncyclic fan of length at least `5`
breaks `3`-connectivity, then the fan can be extended at the beginning to a larger fan. -/
lemma IsFan.exists_extend_of_not_tutteConnected_remove (h : M.IsFan F b c) (h5 : 5 ≤ F.length)
    (hM : M.TutteConnected 3) (hnf : ¬ M.IsCyclicFan F b)
    (ht : ¬ (M.remove b {F[0]}).TutteConnected 3) : ∃ x, M.IsFan (x :: F) (!b) c := by
  have hM5 : 5 ≤ M.E.encard := by
    grw [← h.subset_ground, h.nodup.encard_toSet_eq, ← h5, Nat.cast_ofNat]
  have hM4 : 4 ≤ M.E.encard := by grw [← hM5]; simp
  have hne : M.Nonempty := ⟨F[0], h.subset_ground (by simp)⟩
  obtain ⟨i, hi, ⟨x, hx, hT⟩ | ⟨j, hij, hj, hT⟩⟩ :=
    h.exists_triad_of_not_tutteConnected_three_remove (by lia) hM hnf ht
  · obtain rfl | rfl := Nat.le_one_iff_eq_zero_or_eq_one.1 hi
    · exact ⟨x, h.cons' hx <| by simpa [head_eq_getElem]⟩
    have hcon := (h.isTriangle_getElem 2).mem_or_mem_of_isCircuit_bDual
      (by simpa using hT.isCircuit) (by simp)
    simp [h.nodup.getElem_inj_iff, show F[3] ≠ x by grind, show F[4] ≠ x by grind] at hcon
  have h1 : M.eConn {e | e ∈ F} ≤ 1 := by
    refine h.eConn_le_one_of_mem_closure (mem_of_mem_of_subset hT.mem_closure₁ ?_)
    exact closure_subset_closure _ <| by grind [getElem_mem_tail]
  obtain heq | hssu := h.subset_ground.eq_or_ssubset
  · exact False.elim <| hnf <| And.right <|
      h.isCyclicFan_of_ground_eq (hM.simple hM4) (hM.dual.simple hM4) heq
  obtain rfl | rfl := c.eq_or_eq_not !b
  · refine False.elim <| hnf <| h.isCyclicFan_of_tutteConnected_three_of_mem_closure hM hM4
      <| mem_of_mem_of_subset hT.mem_closure₁ <| closure_subset_closure _ <| ?_
    simp [insert_subset_iff, getElem_mem_tail, getElem_mem_tail _ (by lia) hj]
  obtain hl | hr := hM.encard_eq_or_encard_compl_eq (k := 2) (by grw [h1, one_add_one_eq_two])
    h.subset_ground
  · rw [h.nodup.encard_toSet_eq] at hl
    enat_to_nat! <;> lia
  obtain ⟨x, hxF, hE⟩ : ∃ a, a ∉ F ∧ M.E = insert a {e | e ∈ F} := by
    obtain h0 | ⟨a, h1⟩ := encard_le_one_iff_eq.1 (hr.trans_le h1)
    · exact False.elim <| hssu.ne <| (sdiff_eq_empty.1 h0).antisymm' h.subset_ground
    refine ⟨a, fun haF ↦ (h1.superset rfl).2 haF, ?_⟩
    rw [← singleton_union, ← h1, sdiff_union_of_subset h.subset_ground]
  refine ⟨x, h.cons' hxF ?_⟩
  have hsi {d} : (M.bDual d).Simple := (hM.bDual d).simple (by simpa)
  refine isTriangle_of_dep_of_encard_le ?_
    (by grw [encard_insert_le, encard_pair_le, two_add_one_eq_three])
  rw [← dual_bDual, ← codep_def, ← nonspanning_compl_iff (by grind), bDual_ground,
    ← getElem_zero (by lia), head_tail]
  refine nonspanning_of_eRk_ne <| ne_of_lt ?_
  have hss : M.E \ {x, F[0], F[1]} ⊆ {e | e ∈ F.tail.tail} := by
    rw [sdiff_subset_iff, hE, insert_union, insert_union, singleton_union,
      h.nodup.tail.toSet_tail_eq (by grind), h.nodup.toSet_tail_eq h.ne_nil]
    grind
  grw [hss, ← ENat.mul_lt_mul_left_iff (c := 2) (by simp) (by simp),
    (((h.tail (by lia)).tail (by grind)).bDual b).eRk_le (by grind), ← eRk_le_eRank _ {e | e ∈ F},
    (show M.IsFan F b b by simpa using h).eRk_eq]
  · suffices (F.length : ℕ∞) - 1 - 1 < F.length by simpa
    enat_to_nat! <;> lia
  rw [parallel_iff_eq]
  grind [h.nodup.getElem_inj_iff]

lemma IsFan.remove_tutteConnected_three_of_maximalFor_setOf (hF : M.IsFan F b c)
    (hF4 : 4 ≤ F.length) (hM : M.TutteConnected 3)
    (hmax : MaximalFor (fun L : List α ↦ ∃ b, M.IsFan L b c) (fun L ↦ {e | e ∈ L}) F)
    (hFc : ¬ M.IsCyclicFan F b) : (M.remove b {F[0]}).TutteConnected 3 := by
  by_contra! hcon
  obtain h4 | h4 := hF4.eq_or_lt
  · obtain ⟨x, hx | hx⟩ := hF.exists_extend_of_not_tutteConnected_remove₄ h4.symm hM hFc hcon
    · exact (nodup_cons.1 hx.nodup).1 <| by simpa using hmax.2 ⟨!b, hx⟩ (by grind)
    refine (nodup_cons.1 hx.nodup).1 ?_
    obtain ⟨u, y, z, w, rfl⟩ : ∃ a b c d, F = [a, b, c, d] := by rwa [eq_comm, length_eq_four]
       at h4
    simpa [or_left_comm (a := (x = z))] using hmax.2 ⟨!b, hx⟩
  obtain ⟨x, hx⟩ := hF.exists_extend_of_not_tutteConnected_remove (by lia) hM hFc hcon
  exact (nodup_cons.1 hx.nodup).1 <| by simpa using hmax.2 ⟨!b, hx⟩ (by grind)

lemma IsFan.remove_tutteConnected_three_of_maximalFor_length (hF : M.IsFan F b c)
    (hF4 : 4 ≤ F.length) (hM : M.TutteConnected 3)
    (hmax : MaximalFor (fun L : List α ↦ ∃ b, M.IsFan L b c) length F)
    (hFc : ¬ M.IsCyclicFan F b) : (M.remove b {F[0]}).TutteConnected 3 := by
  by_contra! hcon
  obtain h4 | h4 := hF4.eq_or_lt
  · obtain ⟨x, hx | hx⟩ := hF.exists_extend_of_not_tutteConnected_remove₄ h4.symm hM hFc hcon
    · simpa using hmax.2 ⟨!b, hx⟩ (by simp)
    simpa [h4.symm] using hmax.2 ⟨!b, hx⟩
  obtain ⟨x, hx⟩ := hF.exists_extend_of_not_tutteConnected_remove (by lia) hM hFc hcon
  simpa using hmax.2 ⟨!b, hx⟩

/-- Every fan `F₀` of length at least four in a finite-rank `3`-connected matroid is a suffix of
a fan whose initial element is removable, up to switching the middle two elements of `F₀` if it
has length four.  -/
lemma IsFan.exists_suffix_removable [M.RankFinite] {F₀ : List α} (hF₀ : M.IsFan F₀ b c)
    (hF₀4 : 4 ≤ F₀.length) (hM : M.TutteConnected 3) : ∃ (F F₁ : List α), (F₁ = F₀ ∨ F₀.length = 4 ∧
    F₁ = [F₀[0], F₀[2], F₀[1], F₀[3]]) ∧ F₁ <:+ F ∧ (M.IsCyclicFan F (!c) ∨
      ∃ (d : Bool) (hF : M.IsFan F d c), (M.remove d {F[0]}).TutteConnected 3) := by
  by_cases hF₀r : (M.remove b {F₀[0]}).TutteConnected 3
  · exact ⟨F₀, F₀, .inl rfl, by simp, .inr ⟨b, hF₀, hF₀r⟩⟩
  by_cases hC : M.IsCyclicFan F₀ b
  · refine ⟨F₀, F₀, .inl rfl, by simp, .inl ?_⟩
    rwa [hF₀.bool_right_eq, hC.even, beq_false, Bool.not_not]
  classical
  obtain ⟨x, F₁, hF₁, hF₁_eq⟩ : ∃ x F₁, M.IsFan (x :: F₁) (!b) c ∧
    (F₁ = F₀ ∨ F₀.length = 4 ∧ F₁ = [F₀[0], F₀[2], F₀[1], F₀[3]]) := by
    obtain h4 | h5 := hF₀4.eq_or_lt
    · obtain ⟨x, hx | hx⟩ := hF₀.exists_extend_of_not_tutteConnected_remove₄ h4.symm hM hC hF₀r
      · exact ⟨x, F₀, hx, .inl rfl⟩
      exact ⟨x, _, hx, .inr ⟨h4.symm, rfl⟩⟩
    obtain ⟨x, hx⟩ := hF₀.exists_extend_of_not_tutteConnected_remove (by lia) hM hC hF₀r
    exact ⟨x, F₀, hx, .inl rfl⟩
  set s := {L : List α | (∃ d, M.IsFan L d c) ∧ (x :: F₁) <:+ L} with hs
  have hsfin : (length '' s).Finite := by
    refine BddAbove.finite ⟨2 * (M.rank + 1), ?_⟩
    simp only [upperBounds, hs, mem_image, mem_ofPred_eq, forall_exists_index, and_imp]
    rintro _ L c hL _ rfl
    have hcon := hL.eRk_ge
    grw [← ENat.natCast_le_natCast, Nat.cast_mul, Nat.cast_add, cast_rank_eq, hcon, eRk_le_eRank,
      Bool.toNat_le_one]
    enat_to_nat! <;> simp
  have hsne : s.Nonempty := ⟨x :: F₁, ⟨(!b), hF₁⟩, suffix_refl ..⟩
  obtain ⟨F, hFmax⟩ := Finite.exists_maximalFor' _ _ hsfin hsne
  obtain ⟨⟨d, hF⟩, hF₁F⟩ := hFmax.1
  refine ⟨F, F₁, hF₁_eq, (suffix_cons ..).trans hF₁F, or_iff_not_imp_left.2 fun hFc ↦
    ⟨d, hF, by_contra fun hcon ↦ ?_⟩⟩
  have hnc : ¬ M.IsCyclicFan F d := by
    contrapose! hFc
    simpa [hF.bool_right_eq, hFc.even]
  have h5 : 5 ≤ F.length := by grind [hF₁F.length_le, length_cons]
  obtain ⟨y, hy⟩ := hF.exists_extend_of_not_tutteConnected_remove h5 hM hnc hcon
  simpa using hFmax.2 (j := y :: F) ⟨⟨_, hy⟩, hF₁F.trans (suffix_cons ..)⟩

/-- A version of `IsFan.exists_suffix_removable'` with a stronger hypothesis that `F` has
five elements, and hence a simpler statement.  -/
lemma IsFan.exists_suffix_removable' [M.RankFinite] {F₀ : List α} (hF₀ : M.IsFan F₀ b c)
    (hF₀5 : 5 ≤ F₀.length) (hM : M.TutteConnected 3) : ∃ F, F₀ <:+ F ∧
    (M.IsCyclicFan F (!c) ∨ ∃ (d : Bool) (hF : M.IsFan F d c),
      (M.remove d {F[0]}).TutteConnected 3) := by
  obtain ⟨F, F₁, hF₁, hs, hF⟩ := hF₀.exists_suffix_removable (by lia) hM
  obtain rfl : F₁ = F₀ := by lia
  exact ⟨F, hs, hF⟩

/-- If `M` is a `3`-connected matroid with a fan of `F₀` length at least four, then `F₀`
is a subset of a fan `F` that is either cyclic, or whose initial element can be removed
keeping connectivity. -/
lemma TutteConnected.exists_subset_isFan_remove_tutteConnected_three [M.RankFinite]
    (hM : M.TutteConnected 3) {F₀} (hF₀ : M.IsFan F₀ b c) (hF₀4 : 4 ≤ F₀.length) :
    ∃ F, F₀ ⊆ F ∧ (M.IsCyclicFan F !c ∨
    ∃ (d : Bool) (hF : M.IsFan F d c), (M.remove d {F[0]}).TutteConnected 3) := by
  obtain ⟨F, F₁, hF₁, hF₁F, hF⟩ := hF₀.exists_suffix_removable hF₀4 hM
  refine ⟨F, ?_, hF⟩
  obtain rfl | ⟨h4, rfl⟩ := hF₁
  · exact hF₁F.subset
  obtain ⟨x, y, z, w, rfl⟩ := length_eq_four.1 h4
  simpa [and_left_comm (a := z ∈ F)] using hF₁F.subset
