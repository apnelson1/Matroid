import Matroid.Connectivity.Fan.Rotary
import Matroid.Connectivity.Separation.Tutte
import Matroid.Connectivity.Splitter.TutteTriangle

open Set List

namespace Matroid

variable {α β : Type*} {F : List α} {b c d : Bool} {M : Matroid α}

lemma IsFan.exists_triad_of_not_tutteConnected_three_remove (h : M.IsFan F b c) (h4 : 4 ≤ F.length)
    (hM : M.TutteConnected 3) (hnf : ¬ M.IsRotaryFan F b)
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
  · obtain ⟨-, h⟩ := h.isRotaryFan_of_ground_eq (hM.simple hM4) (hM.dual.simple (by simpa))
      (Finite.eq_of_subset_of_encard_le (by simp) h.subset_ground
        (by grw [← hM4_eq, h.nodup.encard_toSet_eq, ← h4, Nat.cast_ofNat]))
    contradiction
  have aux {x} : 4 ≤ (M.E \ {x}).encard := by
    grw [← ENat.add_one_le_add_one_iff, ← encard_le_encard_sdiff_singleton_add_one,
      Order.add_one_le_of_lt hM5]
  have hF1 : ¬ (M ＼ {F[1]}).TutteConnected 3 := by
    intro hF1
    have hsi : (M✶ ／ {F[1]}).Simple := by simpa using hF1.dual.simple (by simpa using aux)
    have hwin := (h.isTriad_getElem_of_eq 1 (by lia) rfl).parallel_contract₁.eq
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
    (hM : M.TutteConnected 3) (hnf : ¬ M.IsRotaryFan F b)
    (ht : ¬ (M.remove b {F[0]}).TutteConnected 3) :
    ∃ x, M.IsFan (x :: F) (!b) c ∨ M.IsFan [x, F[0], F[2], F[1], F[3]] (!b) c := by
  have hM4 : 4 ≤ M.E.encard := by
    grw [← h.subset_ground, h.nodup.encard_toSet_eq, h4, Nat.cast_ofNat]
  obtain rfl : c = !b := by simpa [h4] using h.bool_right_eq
  by_cases h0 : F[0] ∈ (M.bDual (!b)).closure {x | x ∈ F.tail}
  · exact False.elim <| hnf <| h.isRotaryFan_of_tutteConnected_three_of_mem_closure hM hM4 h0
  obtain ⟨i, hi, ⟨x, hxF, hT⟩ | ⟨j, hij, hj, hT⟩⟩ :=
    h.exists_triad_of_not_tutteConnected_three_remove h4.ge hM hnf ht
  · obtain rfl | rfl := Nat.le_one_iff_eq_zero_or_eq_one.1 hi
    · exact ⟨x, .inl <| h.cons' hxF <| by simpa [head_eq_getElem]⟩
    exact ⟨x, .inr <| (h.swap_middle h4).cons' (by grind [mem_iff_getElem]) (by simpa using hT)⟩
  refine False.elim <| h0 <| mem_of_mem_of_subset hT.mem_closure₁ <| closure_subset_closure _ ?_
  simp [insert_subset_iff, getElem_mem_tail, show j ≠ 0 by lia]

lemma IsFan.exists_extend_of_not_tutteConnected_remove (h : M.IsFan F b c) (h5 : 5 ≤ F.length)
    (hM : M.TutteConnected 3) (hnf : ¬ M.IsRotaryFan F b)
    (ht : ¬ (M.remove b {F[0]}).TutteConnected 3) : ∃ x, M.IsFan (x :: F) (!b) c := by
  have hM5 : 5 ≤ M.E.encard := by
    grw [← h.subset_ground, h.nodup.encard_toSet_eq, ← h5, Nat.cast_ofNat]
  have hM4 : 4 ≤ M.E.encard := by grw [← hM5]; simp
  have hne : M.Nonempty := ⟨F[0], h.subset_ground (by simp)⟩
  obtain ⟨i, hi, ⟨x, hx, hT⟩ | ⟨j, hij, hj, hT⟩⟩ :=
    h.exists_triad_of_not_tutteConnected_three_remove (by lia) hM hnf ht
  · obtain rfl | rfl := Nat.le_one_iff_eq_zero_or_eq_one.1 hi
    · exact ⟨x, h.cons' hx <| by simpa [head_eq_getElem]⟩
    have hcon := h.mem_or_mem₁₂ 2 (C := {x, F[0], F[2]}) (by lia) (by simpa using hT.isCircuit)
      (by simp)
    simp [h.nodup.getElem_inj_iff, show F[3] ≠ x by grind, show F[4] ≠ x by grind] at hcon
  have h1 : M.eConn {e | e ∈ F} ≤ 1 := by
    refine h.eConn_le_one_of_mem_closure (mem_of_mem_of_subset hT.mem_closure₁ ?_)
    exact closure_subset_closure _ <| by grind [getElem_mem_tail]
  obtain heq | hssu := h.subset_ground.eq_or_ssubset
  · exact False.elim <| hnf <| And.right <|
      h.isRotaryFan_of_ground_eq (hM.simple hM4) (hM.dual.simple hM4) heq
  obtain rfl | rfl := c.eq_or_eq_not !b
  · refine False.elim <| hnf <| h.isRotaryFan_of_tutteConnected_three_of_mem_closure hM hM4
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
