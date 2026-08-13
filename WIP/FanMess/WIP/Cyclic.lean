
import Matroid.Connectivity.WIP.Circuit
import Mathlib.Data.ZMod.Basic

open Set List Bool

set_option linter.style.longLine false

variable {α : Type*} {M : Matroid α} {X Y C K T : Set α} {e f g x y : α} {b c d : Bool}
    {k n i j p q r : ℕ} {b c : Bool} {F : M.Fan}

namespace Matroid.Fan

protected structure IsCyclic (F : M.Fan) : Prop where
  length_ge : 4 ≤ F.length
  isTriangle_end : (M.bDual F.b).IsTriangle {F[F.length - 2], F[F.length - 1], F[0]}
  isTriad_end : (M.bDual (!F.b)).IsTriangle {F[F.length - 1], F[0], F[1]}

attribute [grind! .] IsCyclic.length_ge

lemma IsCyclic.length_bodd (hF : F.IsCyclic) : F.length.bodd = false := by
  cases h : F.length.bodd
  · rfl
  have := F.isTriangle 0 (by grind)
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le' hF.length_ge
  have hkb : k.bodd = true := by simpa [hk] using h
  have hT := F.isTriangle_bDual_of_eq (k + 1) F.b (by lia) (by simp [hkb])
  obtain rfl : k = 0 := by
    simpa [hk] using hT.reverse.mem_or_mem_of_isCircuit_bDual hF.isTriad_end.isCircuit
  simp at hkb

lemma IsCyclic.length_sub_one_bodd (hF : F.IsCyclic) : (F.length - 1).bodd = true := by
  simp [F.length_sub_one_bodd_eq, F.right_eq_not hF.length_bodd]

macro_rules
  | `(tactic| get_elem_tactic_extensible) =>
    `(tactic| exact ZMod.val_lt ..)

@[simp]
protected lemma val_one (F : M.Fan) : (1 : ZMod F.length).val = 1 := ZMod.val_one ..

@[simp]
protected lemma IsCyclic.val_two (hF : F.IsCyclic) : (2 : ZMod F.length).val = 2 := by
  rw [ZMod.val_ofNat, Nat.mod_eq_of_lt (by grind)]

@[simp]
protected lemma IsCyclic.val_three (hF : F.IsCyclic) : (3 : ZMod F.length).val = 3 := by
  rw [ZMod.val_ofNat, Nat.mod_eq_of_lt (by grind)]

lemma IsCyclic.add_val_bodd (hF : F.IsCyclic) (a b : ZMod F.length) :
    (a + b).val.bodd = (a.val.bodd != b.val.bodd) := by
  obtain hle | hlt := le_or_gt F.length (a.val + b.val)
  · simp [ZMod.val_add_of_le hle, Nat.bodd_sub hle, hF.length_bodd]
  simp [ZMod.val_add_of_lt hlt]

lemma IsCyclic.add_one_val_bodd (hF : F.IsCyclic) (a : ZMod F.length) :
    (a + 1).val.bodd = !a.val.bodd := by
  simp [hF.add_val_bodd]

lemma IsCyclic.neg_val_bodd (hF : F.IsCyclic) (a : ZMod F.length) :
    (- a).val.bodd = a.val.bodd := by
  simpa using hF.add_val_bodd (-a) a

lemma IsCyclic.mod_bodd (hF : F.IsCyclic) (i : ℕ) : (i % F.length).bodd = i.bodd := by
  rw [← Nat.mod_add_div i F.length, Nat.mod_add_mod, Nat.add_mul_mod_self_left, Nat.bodd_add,
    Nat.bodd_mul]
  simp [hF.length_bodd]

lemma IsCyclic.isTriangle (hF : F.IsCyclic) (i : ZMod F.length) :
    (M.bDual (F.b != i.val.bodd)).IsTriangle {F[i.val], F[(i + 1).val], F[(i + 2).val]} := by
  simp only [ZMod.val_add, Fan.val_one, hF.val_two]
  by_cases hi : i.val + 2 < F.length
  · convert F.isTriangle i.val hi
    all_goals rw [Nat.mod_eq_of_lt (by lia)]
  have hlt := i.val_lt
  obtain hi1 | hi2 : i.val + 1 = F.length ∨ i.val + 2 = F.length := by lia
  · simp_rw [hi1, Nat.mod_self, show i.val + 2 = (i.val + 1) + 1 from rfl, hi1, Nat.add_mod_left,
      Nat.mod_eq_of_lt (show 1 < F.length by grind), show i.val = F.length - 1 by lia,
      F.length_sub_one_bodd_eq, ← Bool.bne_assoc, bne_self_eq_false, false_bne,
      F.right_eq_not hF.length_bodd]
    exact hF.isTriad_end
  simp_rw [hi2, Nat.mod_self, Nat.mod_eq_of_lt (show i.val + 1 < F.length by lia),
    show i.val + 1 = F.length - 1 by lia, show i.val = F.length - 2 by lia,
    Nat.bodd_sub F.length_ge_two, hF.length_bodd]
  simpa using hF.isTriangle_end

@[simps!]
def rotate (F : M.Fan) (hF : F.IsCyclic) (k : ℕ) : M.Fan where
  toList := (F : List α).rotate k
  b := F.b != k.bodd
  c := F.c != k.bodd
  toList_nodup := nodup_rotate.2 F.nodup
  toList_length_ge := by simpa using F.length_ge_two
  toList_length_bodd := by cases h : F.b with simp [F.right_eq_not, hF.length_bodd, h]
  isNonloop' := by simp [show F.length ≠ 2 by grind]
  isTriangle' i hi := by
    simp only [bne_assoc, getElem_rotate, length_toList, getElem_toList']
    convert hF.isTriangle (i + k)
    · simp [hF.add_val_bodd, hF.mod_bodd, bne_comm]
    · simp [ZMod.val_add]
    · simp [ZMod.val_add, add_right_comm]
    simp [ZMod.val_add, add_right_comm, hF.val_two]

@[simp, grind! .]
lemma rotate_length (F : M.Fan) (hF) : (F.rotate hF k).length = F.length := by
  simp [← length_toList]

@[simp]
lemma rotate_getElem_val (F : M.Fan) (hF) (k) (i : ZMod F.length) :
    (F.rotate hF k)[i.val] = F[(i + k).val] := by
  rw [← getElem_toList]
  simp [ZMod.val_add]

lemma rotate_getElem (F : M.Fan) (hF k i) (hi : i < (F.rotate hF k).length) :
    (F.rotate hF k)[i] = F[((i : ZMod F.length) + k).val] := by
  simp_rw [← rotate_getElem_val F hF, ZMod.val_natCast,
    Nat.mod_eq_of_lt (show i < F.length by grind)]

lemma IsCyclic.rotate_isCyclic (hF : F.IsCyclic) (k : ℕ) : (F.rotate hF k).IsCyclic := by
  refine ⟨by simpa using hF.length_ge, ?_, ?_⟩
  · simp_rw [rotate_left, rotate_length, rotate_getElem, ← Nat.cast_add, zero_add]
    convert hF.isTriangle (F.length - 2 + k) using 3
    · simp only [CharP.cast_eq_zero, zero_sub, hF.add_val_bodd]
      simp [hF.neg_val_bodd, hF.mod_bodd, hF.val_two]
    · rw [Nat.cast_add, Nat.cast_sub (by grind), Nat.cast_two]
    · convert rfl
      rw [Nat.cast_add, Nat.cast_sub (by grind)]
      grind
    convert rfl
    simp
  simp_rw [rotate_left, bnot_bne, rotate_length, rotate_getElem, ← Nat.cast_add, zero_add]
  convert hF.isTriangle (F.length - 1 + k)
  · simp [hF.add_val_bodd, hF.neg_val_bodd, hF.mod_bodd]
  · rw [Nat.cast_add, Nat.cast_sub (by grind), Nat.cast_one]
  · rw [← add_sub_right_comm, sub_add_cancel]
    simp
  simp only [Nat.cast_add, CharP.cast_eq_zero]
  ring

lemma length_ge_four_of_eq_ground (F : M.Fan) (hM : M.Simple) (hM' : M✶.Simple)
    (hFE : (F : Set α) = M.E) : 4 ≤ F.length := by
  have hF2 := F.length_ge_two
  have hr := M.eRk_pair_eq (e := F[0]) (f := F[1]) (by simp) (by simp) (by simp)
  have hr1 := M✶.eRk_pair_eq (e := F[0]) (f := F[1]) (by simp) (by simp) (by simp)
  have hle := encard_le_encard hFE.symm.subset
  grw [← eRank_add_eRank_dual, ← M.eRk_le_eRank {F[0], F[1]},
    ← M✶.eRk_le_eRank {F[0], F[1]}, hr, hr1, F.encard_toSet_eq,
    show (2 : ℕ∞) + 2 = 4 from rfl, Nat.ofNat_le_cast] at hle
  assumption

/-- A fan on the ground set of a simple, cosimple matroid is rotary. -/
lemma end_triangle_of_eq_ground (F : M.Fan) (hE : (F : Set α) = M.E)
    (hsi : ∀ d, (M.bDual d).Simple) : F.length.bodd = false
    ∧ (M.bDual !F.b).IsTriangle {F[0], F[1], F.getLast} := by
  have h4 := F.length_ge_four_of_eq_ground (hsi false) (hsi true) hE
  have hi := (F.bDual F.b).jointsBetween_indep (p := 0) (q := F.length - (!F.length.bodd).toNat)
    (by grind) (by grind) fun _ _ _ _ h ↦ F.getLast_ne_get_zero.symm h.eq
  rw [jointsBetween_bDual, bne_false] at hi
  have hcl := hi.notMem_closure_sdiff_of_mem (e := F[0])
    <| by simp [getElem_mem_jointsBetween_iff, show (!F.length.bodd).toNat < F.length by grind]
  grw [← jointsBetween_add_one_left_eq_sdiff (by grind),
    ← jointsBetween_add_one_left_eq_self (by simp) (by grind), zero_add, one_add_one_eq_two] at hcl
  have hclss := (F.bDual F.b).getElems_Ico_subset_closure_jointsBetween (p := 2)
    (q := F.length - (!F.length.bodd).toNat) (by simp)
    (by simp [Nat.bodd_sub (show (!F.length.bodd).toNat ≤ F.length by grind)])
    (by simp) (by grind)
  simp only [jointsBetween_bDual, bne_false] at hclss
  grw [← closure_closure, ← hclss, bDual_toList, show M.bDual F.b = (M.bDual !F.b)✶ by simp,
    mem_dual_closure_iff_forall_isCircuit, ← getElems_Ico] at hcl
  simp [not_forall, ← not_disjoint_iff_nonempty_inter, ] at hcl
  obtain ⟨C, hC, h0C, hdj⟩ := hcl
  have hCF := (hC.subset_ground.trans_eq (by simpa using hE.symm))
  obtain ⟨J, hJ, rfl⟩ := exists_eq_getElems hCF
  rw [F.nodup.getElems_disjoint_iff, disjoint_iff_inter_eq_empty, inter_comm J,
    ← inter_assoc, inter_assoc _ _ (Iio _), inter_self, Ico_inter_Iio, min_eq_left (by lia),
    ← disjoint_iff_inter_eq_empty, _root_.disjoint_comm] at hdj
  replace hJ := subset_sdiff.2 ⟨hJ, hdj⟩
  simp only [length_toList, Set.subset_def, mem_sdiff, mem_Iio, mem_Ico, _root_.not_and, not_lt,
    tsub_le_iff_right, forall_mem_and] at hJ
  have hJsss : J ⊆ {0, 1, F.length - (!F.length.bodd).toNat} := by grind
  have hT := isTriangle_of_dep_of_encard_le hC.dep <| by
    grw [getElems_encard_le, hJsss, encard_triple_le]
  obtain ⟨rfl, hodd⟩ : J = {0, 1, F.length - 1} ∧ F.length.bodd = false := by
    have h3 := hT.three_elements.ge
    grw [F.nodup.getElems_encard_eq, inter_subset_left] at h3
    have h_eq := Finite.eq_of_subset_of_encard_le' (by simp) hJsss ((encard_triple_le ..).trans h3)
    cases hf : F.length.bodd
    · exact ⟨by simp [h_eq, hf], rfl⟩
    simpa using hJ.1 F.length (by simp [h_eq, hf])
  rw [getElems_insert _ _ (by lia), getElems_insert _ _ (by lia), getElems_singleton (by lia),
    getElem_toList, getElem_toList, getElem_toList, ← getLast_eq_getElem] at hT
  rwa [and_iff_right hodd]

/-- A fan on the ground set of a simple, cosimple matroid is cyclic. -/
lemma IsFan.isCyclic_of_eq_ground (F : M.Fan) (hM : M.Simple) (hM' : M✶.Simple)
    (hE : (F : Set α) = M.E) : F.IsCyclic := by
  obtain ⟨hb, ht⟩ := F.end_triangle_of_eq_ground (by simpa) (fun d ↦ by cases d with simpa)
  obtain ⟨-, ht'⟩ := F.reverse.end_triangle_of_eq_ground (by simpa) (fun d ↦ by cases d with simpa)
  simp only [reverse_left, reverse_getElem_zero, reverse_getElem_one, reverse_getLast] at ht'
  have h4 := F.length_ge_four_of_eq_ground hM hM' hE
  refine ⟨h4, ?_, ?_⟩
  · rwa [← getPenult, ← getLast_eq_getElem, insert_comm, F.left_eq, hb, beq_false]
  rwa [insert_comm, pair_comm, ← getLast_eq_getElem]

lemma IsCyclic.eConn_eq_zero (hF : F.IsCyclic) : M.eConn (F : Set α) = 0 := by
  refine F.eConn_eq_zero_of_mem_closure_mem_closure hF.length_bodd ?_ ?_
  · refine mem_of_mem_of_subset hF.isTriad_end.swap_left.mem_closure₁ <| closure_subset_closure _ ?_
    simp [insert_subset_iff, show F.length - 1 ≠ 0 by grind]
  rw [getLast_eq_getElem]
  refine mem_of_mem_of_subset hF.isTriangle_end.mem_closure₂ <| closure_subset_closure _ ?_
  simp [insert_subset_iff, show F.length - 2 ≠ F.length - 1 by grind,
    show 0 ≠ F.length - 1 by grind]

lemma IsCyclic.setOf_eq_ground (hF : F.IsCyclic) (hM : M.TutteConnected 2) : (F : Set α) = M.E := by
  have hne : M.Nonempty := ⟨F[0], by simp⟩
  exact (hM.connected rfl.le).eq_ground_of_eConn_eq_zero hF.eConn_eq_zero ⟨F[0], by simp⟩
    F.subset_ground

lemma IsCyclic.reverse (hF : F.IsCyclic) : F.reverse.IsCyclic where
  length_ge := by simpa using hF.length_ge
  isTriangle_end := by
    rw [← getPenult, ← getLast_eq_getElem, reverse_getPenult, reverse_getLast, reverse_getElem_zero,
      reverse_left, F.right_eq_not hF.length_bodd, getLast_eq_getElem]
    exact hF.isTriad_end.reverse
  isTriad_end := by
    rw [← getLast_eq_getElem, reverse_getLast, reverse_getElem_zero, reverse_getElem_one,
      reverse_left, ← F.left_eq_not hF.length_bodd, getLast_eq_getElem]
    exact hF.isTriangle_end.reverse

lemma IsCyclic.restrict_connected (hF : F.IsCyclic) : (M ↾ F).Connected := by
  wlog hb : F.b = false generalizing F with aux
  · obtain hb' : F.b = true := by grind
    simpa using aux hF.reverse (by simpa [F.right_eq_not hF.length_bodd])
  refine connected_iff_exists.2 ⟨F[0], by simp, fun f hf ↦ ?_⟩
  obtain ⟨rfl | i, hi, rfl⟩ := F.getElem_of_mem hf
  · simp
  suffices hC : ∃ C ⊆ {e | e ∈ F}, M.IsCircuit C ∧ F[0] ∈ C ∧ F[i + 1] ∈ C by
    obtain ⟨C, hCss, hC, h0C, hiC⟩ := hC
    exact (hC.isCircuit_restrict_of_subset hCss).mem_connectedTo_mem h0C hiC
  obtain hi' | hne := eq_or_ne (i + 2) F.length
  · exact ⟨_, by simp [insert_subset_iff], hb ▸ hF.isTriangle_end.isCircuit, by simp,
      by simp [← hi']⟩
  have hC := F.isCircuit_interval 0 (i + 1 + (!i.bodd).toNat) (by lia) (by grind) (by simpa)
    (by simpa) (by simp [F.right_eq_not hF.length_bodd, hb])
  refine ⟨_, ?_, hC, by simp, ?_⟩
  · simp [insert_subset_iff, jointsBetween_subset]
  obtain hib | hib := i.bodd.eq_false_or_eq_true
  · simp [hib]
  simpa [hib, getElem_mem_jointsBetween_iff]

/-- A rotary fan is the entire matroid iff the matroid is connected. -/
lemma IsCyclic.setOf_eq_ground_iff (hF : F.IsCyclic) : (F : Set α) = M.E ↔ M.Connected := by
  refine ⟨fun h ↦ ?_, fun h ↦ hF.setOf_eq_ground h.tutteConnected_two⟩
  rw [← M.restrict_ground_eq_self]
  exact h ▸ hF.restrict_connected


lemma IsCyclic.restrict (hF : F.IsCyclic) :
    (F.restrict F hF.length_ge rfl.subset (by
      intro hb


      )
      sorry).IsCyclic := by
  sorry


lemma IsCyclic.restrict_self (h : M.IsCyclic F b) : (M ↾ {e | e ∈ F}).IsRotaryFan F b := by
  have aux {c : Bool} {T} (hTF : T ⊆ {e | e ∈ F}) (hT : (M.bDual c).IsTriangle T) :
      ((M ↾ {e | e ∈ F}).bDual c).IsTriangle T := by
    obtain rfl | rfl := c
    · rwa [bDual_false, isTriangle_restrict_iff, and_iff_left hTF]
    rw [← Skew.contract_restrict_eq (X := M.E \ {e | e ∈ F}), restrict_eq_self_iff.2]
    · grw [bDual_true, dual_contract, isTriangle_delete_iff, and_iff_right (by simpa),
        sdiff_subset_compl, disjoint_compl_right_iff, hTF]
    · exact Eq.symm <| sdiff_sdiff_cancel_left h.isFan.subset_ground
    rw [skew_comm, ← eConn_eq_zero_iff_skew_compl h.isFan.subset_ground, h.eConn_eq]
  refine ⟨(isFan_iff_forall (by grind)).2 ?_, aux (by grind) h.isTriangle, aux (by grind) h.isTriad⟩
  simp only [Bool.beq_not_self, h.isFan.length_bodd_eq, h.isFan.nodup, true_and]
  exact fun i hi ↦ aux (by grind) <| h.isFan.isTriangle_getElem i hi


#exit
