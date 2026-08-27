module

public import Matroid.Connectivity.Fan.Basic
public import Matroid.Connectivity.Triangle
public import Matroid.Connectivity.Separation.Vertical
public import Mathlib.Order.Interval.Set.Fin

@[expose] public section

set_option linter.style.longLine false

variable {α : Type*} {M : Matroid α} {X Y C K T : Set α} {e f g x y : α} {b c d : Bool}
    {J : Bool → List α} {L : List α} {n i j p q r : ℕ} {F J : List α} {b c : Bool}



open Set List

namespace Matroid

/- Contractions preserve the property of being a fan, unless one of the ends is a joint
spanned by the contract-set. -/
lemma IsFan.contract (hF : M.IsFan F b c) (X : Set α) (hX : _root_.Disjoint {e | e ∈ F} X)
    (h0 : b = false → F[0] ∉ M.closure X) (hlast : c = false → F[F.length - 1] ∉ M.closure X)
    (h3 : F.length = 3 → b = false → c = false → M.Skew {e | e ∈ F} (X ∩ M.E) := by lia) :
    (M ／ X).IsFan F b c := by
  have hFX : ∀ {i} {hi : i < F.length}, F[i] ∉ X := by grind
  refine isFan_of_eq_of_forall_isCircuit hF.two_le_length hF.nodup (by simp [hF.length_bodd_eq])
    ?_ fun i hi ↦ ?_
  · rintro hF2 i hi
    · obtain rfl | rfl := b
      · obtain rfl | rfl : i = 0 ∨ i = 1 := by grind
        · simp [h0, hF.getElem_mem_ground]
        simpa [hFX] using hF.dual.isNonloop_getElem 1 hi (by simp)
      obtain rfl | rfl : i = 0 ∨ i = 1 := by grind
      · simpa [hFX] using hF.dual.isNonloop_getElem 0 hi (by simp)
      have h1cl : F[1] ∉ M.closure X := by simpa [hF.bool_right_eq, hF2] using hlast
      simpa [hF.getElem_mem_ground]
  obtain rfl | hb := b.eq_or_eq_not !i.bodd
  · simpa [hFX] using (hF.isTriangle_getElem i (by lia)).isCircuit
  suffices hsk : M.Skew {F[i], F[i + 1], F[i + 2]} (X ∩ M.E) by
    simpa [hb] using ((hF.isTriangle_getElem_of_eq i (by simp [hb])).contract_isTriangle
      hsk.symm).isCircuit
  -- clear hX
  wlog h1 : i + 3 ≠ F.length generalizing i F b c with aux
  · replace h1 : i + 3 = F.length := by simpa using h1
    obtain rfl | i := i
    · exact (h3 (by simp [← h1]) (by simp [hb])
        (by simp [hF.bool_right_eq, hb, ← h1])).mono_left <| by simp [insert_subset_iff]
    specialize aux hF.reverse (by simpa) (by simpa) (by grind)
      (fun h hc hb ↦ by simpa using h3 (by simpa using h) hb hc) (by grind) 0 (by grind)
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

/-- If `N` is a minor of `M`, and `F` is a fan of `M` contained in `E(N)`, whose (co)joint ends are
are not (co)loops of `N`, then `F` is also a fan of `N`.  -/
lemma IsFan.minor {N : Matroid α} (hF : M.IsFan F b c) (h4 : 4 ≤ F.length) (hNM : N ≤m M)
    (hFN : {e | e ∈ F} ⊆ N.E) (h_first : (N.bDual b).IsNonloop F[0])
    (h_last : (N.bDual c).IsNonloop F[F.length - 1]) : N.IsFan F b c := by
  obtain ⟨C, D, hC, hD, hCD, rfl⟩ := hNM.exists_eq_contract_delete_disjoint
  have hCF := hF.contract (X := C) (by grind) ?_ ?_
  · have hwin := (hCF.dual.contract (X := D) (by grind) ?_ ?_).dual
    · simpa using hwin
    · simp only [Bool.not_eq_eq_eq_not, Bool.not_false, dual_contract, delete_closure_eq, mem_sdiff,
        not_and, not_not, hCD.sdiff_eq_right]
      rintro rfl hcl
      refine False.elim <| h_first.not_isLoop ?_
      grind [bDual_true, dual_delete, dual_contract, contract_isLoop_iff_mem_closure,
        delete_closure_eq, hCD.sdiff_eq_right]
    simp only [Bool.not_eq_eq_eq_not, Bool.not_false, dual_contract, delete_closure_eq, mem_sdiff]
    rintro rfl hcl
    refine h_last.not_isLoop ?_
    grind [bDual_true, dual_delete, dual_contract, contract_isLoop_iff_mem_closure,
      delete_closure_eq]
  · rintro rfl hcl
    grind [bDual_false, delete_isLoop_iff, contract_isLoop_iff_mem_closure, h_first.not_isLoop]
  rintro rfl hcl
  grind [h_last.not_isLoop, bDual_false, delete_isLoop_iff, contract_isLoop_iff_mem_closure]

lemma isFan_delete_iff_of_subset_loops {X : Set α} (hX : X ⊆ M.loops)
    (hFX : _root_.Disjoint X {e | e ∈ F}) : (M ＼ X).IsFan F b c ↔ M.IsFan F b c := by
  have hrw (C : Set α) (d : Bool) (hCX : Disjoint X C) :
      ((M ＼ X).bDual d).IsCircuit C ↔ (M.bDual d).IsCircuit C := by
    cases d
    · simp [hCX.symm]
    simp only [bDual_true, dual_delete]
    rw [contract_eq_delete_of_subset_coloops (by simpa), delete_isCircuit_iff,
      and_iff_left hCX.symm]
  simp only [isFan_iff_forall']
  convert Iff.rfl using 7 with a i i
  · convert Iff.rfl using 2 with hi
    rw [isNonloop_iff, ← singleton_isCircuit, hrw _ _ (by grind), bDual_ground, delete_ground,
      mem_sdiff, isNonloop_iff, ← singleton_isCircuit, bDual_ground,
      and_iff_left (show F[i] ∉ X by grind)]
  rw [hrw _ _ (hFX.mono_right (by grind))]

/- Restrict usually preserve the property of being a fan -/
lemma IsFan.restrict (hF : M.IsFan F b c) (X : Set α) (hX : {e | e ∈ F} ⊆ X)
    (h0 : b = true → F[0] ∈ M.closure (X \ {F[0]}))
    (hlast : c = true → F[F.length - 1] ∈ M.closure (X \ {F[F.length - 1]}))
    (h3 : F.length = 3 → b = true → c = true → M✶.Skew {e | e ∈ F} (M.E \ X) := by lia) :
    (M ↾ X).IsFan F b c := by
  wlog hXE : X ⊆ M.E generalizing X with aux
  · specialize aux (X ∩ M.E) (subset_inter hX hF.subset_ground)
    rw [inter_sdiff_right_comm, inter_sdiff_right_comm, closure_inter_ground, closure_inter_ground,
      imp_iff_right h0, imp_iff_right hlast, sdiff_inter_self_eq_sdiff, imp_iff_right h3,
      imp_iff_right inter_subset_right] at aux
    rwa [← isFan_delete_iff_of_subset_loops (X := X \ M.E), delete_eq_restrict, restrict_ground_eq,
      restrict_restrict_eq _ sdiff_subset, sdiff_sdiff_right_self]
    · grw [restrict_loops_eq', ← subset_union_right]
    grw [hF.subset_ground]
    exact disjoint_sdiff_left
  rw [← delete_compl, ← b.not_not, ← c.not_not, ← isFan_dual_iff, dual_delete]
  refine hF.dual.contract _ (disjoint_sdiff_right.mono_left hX) ?_ ?_ ?_
  · rwa [Bool.not_eq_eq_eq_not, Bool.not_false,
      mem_dual_closure_iff_notMem_closure_compl, sdiff_sdiff_cancel_left hXE, not_not]
    simp [show F[0] ∈ X from hX (by simp)]
  · rwa [Bool.not_eq_eq_eq_not, Bool.not_false,
      mem_dual_closure_iff_notMem_closure_compl, sdiff_sdiff_cancel_left hXE, not_not]
    simp [show F[F.length - 1] ∈ X from hX (by simp)]
  simpa [inter_eq_self_of_subset_left sdiff_subset]

/-- Contracting the head of a fan usually gives a fan on the tail. -/
lemma IsFan.contract_head (hF : M.IsFan F b c) (hF3 : 3 ≤ F.length)
    (h_init : b = true → ¬ M.Parallel F[0] F[1])
    (h_false : b = false → c = false → ¬ M.Parallel F[0] F[F.length - 1])
    (h4 : F.length = 4 → b = true → ¬ F[0] ∈ M.closure {F[1], F[2]} := by lia) :
    (M ／ {F[0]}).IsFan F.tail (!b) c := by
  have aux := @IsFan.contract _ M F.tail _ _ (hF.tail hF3) {F[0]}
    (by simp [getElem_zero_eq_head, hF.nodup.head_notMem_tail])
  simp only [Bool.not_eq_eq_eq_not, Bool.not_false, getElem_tail, zero_add, getElem_mem,
    ← IsNonloop.parallel_iff_mem_closure (hF.isNonloop _), parallel_comm (f := F[0]), length_tail,
    show F.length - 1 - 1 + 1 = F.length - 1 by lia, Nat.pred_eq_succ_iff, Nat.reduceAdd,
    imp_iff_right h_init, singleton_inter_of_mem hF.getElem_mem_ground] at aux
  refine aux ?_ ?_
  · rintro rfl hpara
    obtain rfl | rfl := b
    · exact h_false rfl rfl hpara
    have hwin := (hF.isTriangle_getElem 0 (by lia)).isCircuit.mem_iff_mem_of_parallel_bDual hpara
    obtain h3' : F.length = 3 := by simpa
      [hF.nodup.getElem_inj_iff, show F.length - 1 ≠ 0 by lia, show F.length ≠ 2 by lia] using hwin
    simpa [h3'] using hF.length_bodd_eq
  rintro hF4 rfl rfl
  rw! [(hF.isNonloop (by simp)).skew_right_iff (hF.tail hF3).subset_ground,
    (eq_of_length_eq_three (l := F.tail)) (by grind), getElem_tail, getElem_tail, getElem_tail]
  refine notMem_subset ?_ (h4 hF4 rfl)
  suffices M.closure {F[3], F[2], F[1]} ⊆ M.closure {F[1], F[2]} by simpa [ofPred_or]
  rw [pair_comm, closure_insert_eq_of_mem_closure]
  exact (hF.isTriangle_getElem_of_eq 1 rfl).mem_closure₃

lemma IsFan.delete_head (hF : M.IsFan F b c) (h3 : 3 ≤ F.length)
    (h_init : b = false → ¬ M✶.Parallel F[0] F[1])
    (h_pair : b = true → c = true → ¬ M✶.Parallel F[0] F[F.length - 1])
    (h4 : F.length = 4 → b = false → ¬ F[0] ∈ M✶.closure {F[1], F[2]} := by lia) :
    (M ＼ {F[0]}).IsFan F.tail (!b) c := by
  simpa using (hF.dual.contract_head (by lia) (by simpa) (by simpa)).dual

lemma IsFan.remove_head (hF : M.IsFan F b c) (h3 : 3 ≤ F.length) {d : Bool}
    (h_init : b = d → ¬ (M.bDual !d).Parallel F[0] F[1])
    (h_pair : b = !d → c = !d → ¬ (M.bDual !d).Parallel F[0] F[F.length - 1])
    (h4 : F.length = 4 → b = d → ¬ F[0] ∈ (M.bDual !d).closure {F[1], F[2]} := by lia):
    (M.remove d {F[0]}).IsFan F.tail (!b) c := by
  obtain rfl | rfl := d
  · exact hF.delete_head h3 (by simpa) (by simpa) (by simpa using h4)
  exact hF.contract_head h3 (by simpa) (by simpa) (by simpa using h4)
