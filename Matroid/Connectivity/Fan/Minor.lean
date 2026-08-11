import Matroid.Connectivity.Fan.Basic
import Matroid.Connectivity.Triangle
import Matroid.Connectivity.Separation.Vertical
import Mathlib.Order.Interval.Set.Fin


set_option linter.style.longLine false

variable {α : Type*} {M : Matroid α} {X Y C K T : Set α} {e f g x y : α} {b c d : Bool}
    {J : Bool → List α} {L : List α} {n i j p q r : ℕ} {F J : List α} {b c : Bool}



open Set List

namespace Matroid

/- Contractions preserve the property of being a fan, unless one of the ends is a joint
spanned by the contract-set. -/
lemma IsFan.contract (hF : M.IsFan F b c) (X : Set α) (hX : _root_.Disjoint {e | e ∈ F} X)
    (h0 : b = false → F[0] ∉ M.closure X) (hlast : c = false → F[F.length - 1] ∉ M.closure X)
    (h2 : F.length = 2 → F[(!b).toNat] ∉ M.closure X := by lia)
    (h3 : F.length = 3 → b = false → c = false → M.Skew {e | e ∈ F} (X ∩ M.E) := by lia) :
    (M ／ X).IsFan F b c := by
  refine isFan_of_eq_of_forall_triangle hF.two_le_length hF.nodup (by simp [hF.length_bodd_eq])
    ?_ fun i hi ↦ ?_
  · rintro hF2 (rfl | rfl) i hi
    · obtain rfl | rfl := b
      · obtain rfl | rfl : i = 0 ∨ i = 1 := by grind
        · simp [h0, hF.getElem_mem_ground]
        simpa [hF.getElem_mem_ground] using h2 hF2
      obtain rfl | rfl : i = 0 ∨ i = 1 := by grind
      · simpa [hF.getElem_mem_ground] using h2 hF2
      have h1cl : F[1] ∉ M.closure X := by simpa [hF.bool_right_eq, hF2] using hlast
      simpa [hF.getElem_mem_ground]
    simpa [hX.notMem_of_mem_left] using hF.isNonloop_bDual (e := F[i]) (by simp) true
  obtain rfl | hb := b.eq_or_eq_not !i.bodd
  · simpa [hX.notMem_of_mem_left] using hF.isTriangle_getElem i (by lia)
  suffices hsk : M.Skew {F[i], F[i + 1], F[i + 2]} (X ∩ M.E) by
    simpa [hb] using (hF.isTriangle_getElem_of_eq i (by simp [hb])).contract_isTriangle
      hsk.symm
  clear h2
  wlog h1 : i + 3 ≠ F.length generalizing i F b c with aux
  · replace h1 : i + 3 = F.length := by simpa using h1
    obtain rfl | i := i
    · exact (h3 (by simp [← h1]) (by simp [hb])
        (by simp [hF.bool_right_eq, hb, ← h1])).mono_left <| by simp [insert_subset_iff]
    specialize aux hF.reverse (by simpa) (by simpa) (by simpa)
      (fun h hc hb ↦ by simpa using h3 (by simpa using h) hb hc) 0 (by grind)
      (by simp [hF.bool_right_eq, hb, ← h1]) (by grind)
    rw [pair_comm, insert_comm, pair_comm]
    cases b with simpa [hF.bool_right_eq, ← h1] using aux
  by_contra hnsk
  have hT := hF.isTriangle_getElem_of_eq i (by simp [hb])
  obtain ⟨C, hC, hCss, hiC, hne⟩ := hT.isCircuit.exists_isCircuit_mem_subset_union_of_not_skew
    (e := F[i]) (hX.mono (by simp [insert_subset_iff]) inter_subset_left) hnsk (by simp)
  have hi2C : F[i + 3] ∉ C :=
    fun h ↦ by simpa [hX.notMem_of_mem_left, hF.nodup.getElem_inj_iff, add_assoc] using hCss h
  have hT' := hF.isTriad_getElem_of_eq (i + 1) (by simp [hb])
  obtain ⟨hi2, hi1⟩ | ⟨hi2, hi1⟩ := iff_iff_and_or_not_and_not.1
    <| hT'.reverse.mem_iff_mem_of_isCircuit hC (by simpa)
  · obtain rfl := hT.isCircuit.eq_of_subset_isCircuit hC
      (by simp [insert_subset_iff, hiC, hi1, hi2])
    exact hne.ne_empty <| (hX.mono (by simp [insert_subset_iff]) inter_subset_left).inter_eq
  obtain rfl | i := i
  · grw [insert_comm, insert_union, subset_insert_iff_of_notMem hi1, pair_comm,
      insert_union, subset_insert_iff_of_notMem hi2, ← sdiff_subset_iff,
      Set.inter_subset_left] at hCss
    exact h0 (by simpa) <| mem_of_mem_of_subset (hC.mem_closure_sdiff_singleton_of_mem hiC) <|
      M.closure_subset_closure hCss
  rw [(hF.isTriad_getElem_of_eq i (by simp [hb])).reverse.mem_iff_mem_of_isCircuit hC hi1] at hiC
  simpa [hX.notMem_of_mem_left, hF.nodup.getElem_inj_iff, add_assoc] using hCss hiC

lemma IsFan.contract_head (hF : M.IsFan F b c) (hF3 : 3 ≤ F.length)
    (h_init : b = true → ¬ M.Parallel F[0] F[1])
    (h_false : b = false → c = false → ¬ M.Parallel F[0] F[F.length - 1])
    (h4 : ∀ (hF : F.length = 4), b = true → ¬ F[0] ∈ M.closure {F[1], F[2]} := by lia)
    (h3 : ∀ (hF : F.length = 3), b = true → ¬ M.Parallel F[0] F[2] := by lia) :
    (M ／ {F[0]}).IsFan F.tail (!b) c := by
  have aux := @IsFan.contract _ M F.tail _ _ (hF.tail hF3) {F[0]}
    (by simp [getElem_zero_eq_head, hF.nodup.head_notMem_tail])
  simp only [Bool.not_eq_eq_eq_not, Bool.not_false, getElem_tail, zero_add, getElem_mem,
    ← IsNonloop.parallel_iff_mem_closure (hF.isNonloop _), parallel_comm (f := F[0]), length_tail,
    show F.length - 1 - 1 + 1 = F.length - 1 by lia, Nat.pred_eq_succ_iff, Nat.reduceAdd,
    Bool.not_not, singleton_inter_of_mem hF.getElem_mem_ground] at aux
  refine aux h_init ?_ ?_ ?_
  · rintro rfl hpara
    obtain rfl | rfl := b
    · exact h_false rfl rfl hpara
    have hwin := (hF.isTriangle_getElem 0 (by lia)).isCircuit.mem_iff_mem_of_parallel_bDual hpara
    obtain h3' : F.length = 3 := by simpa
      [hF.nodup.getElem_inj_iff, show F.length - 1 ≠ 0 by lia, show F.length ≠ 2 by lia] using hwin
    exact h3 h3' rfl <| by simpa [h3'] using hpara
  · obtain rfl | rfl := b
    · exact fun h3 hpara ↦ by simpa [hF.nodup.getElem_inj_iff] using
        (hF.isTriangle_getElem 0 (by lia)).notMem_of_mem_of_parallel hpara
    simpa using h3
  rintro hF4 rfl rfl
  rw! [(hF.isNonloop (by simp)).skew_right_iff (hF.tail hF3).subset_ground,
    (eq_of_length_eq_three (l := F.tail)) (by grind), getElem_tail, getElem_tail, getElem_tail]
  refine notMem_subset ?_ (h4 hF4 rfl)
  suffices M.closure {F[3], F[2], F[1]} ⊆ M.closure {F[1], F[2]} by simpa [ofPred_or]
  rw [pair_comm, closure_insert_eq_of_mem_closure]
  exact (hF.isTriangle_getElem_of_eq 1 rfl).mem_closure₃

lemma IsFan.delete_head (hF : M.IsFan F b c) (h5 : 5 ≤ F.length)
    (h_init : b = false → ¬ M✶.Parallel F[0] F[1])
    (h_pair : b = true → c = true → ¬ M✶.Parallel F[0] F[F.length - 1]) :
    (M ＼ {F[0]}).IsFan F.tail (!b) c := by
  simpa using (hF.dual.contract_head (by lia) (by simpa) (by simpa)).dual

lemma IsFan.remove_head (hF : M.IsFan F b c) (h5 : 5 ≤ F.length) {d : Bool}
    (h_init : b = d → ¬ (M.bDual !d).Parallel F[0] F[1])
    (h_pair : b = !d → c = !d → ¬ (M.bDual !d).Parallel F[0] F[F.length - 1]) :
    (M.remove d {F[0]}).IsFan F.tail (!b) c := by
  obtain rfl | rfl := d
  · exact hF.delete_head h5 (by simpa) (by simpa)
  exact hF.contract_head (by lia) (by simpa) (by simpa)
