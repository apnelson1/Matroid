import Matroid.Connectivity.WIP.Minor
import Matroid.Connectivity.Triangle
import Matroid.Connectivity.Separation.Vertical
import Matroid.ForMathlib.List.Set

open Set List Bool

set_option linter.style.longLine false

variable {α : Type*} {M : Matroid α} {X Y C K T : Set α} {e f g x y : α} {b c d : Bool}
    {n i j p q r : ℕ} {b c : Bool} {F : M.Fan}

namespace Matroid.Fan

/-- Get the `d`-joints with indices between `p` and `q` in the cyclic order. -/
def jointsBetween (F : M.Fan) (p q : ℕ) (d : Bool) : Set α :=
    (F : List α).getElems {i | ((p ≤ i ∧ i < q) ∨ (q ≤ p ∧ (i < q ∨ p ≤ i))) ∧ i.bodd = (F.b != d)}

lemma getElem_mem_jointsBetween_iff {hi : i < F.length} :
      F[i] ∈ F.jointsBetween p q d ↔
      ((p ≤ i ∧ i < q) ∨ (q ≤ p ∧ (i < q ∨ p ≤ i))) ∧ i.bodd = (F.b != d) := by
  simp only [jointsBetween, mem_toList_getElems_iff, mem_ofPred_eq]
--     simp [jointsBetween, mem_zipIdx_iff_getElem?, getElem?_eq_some_iff, hi]

lemma getElem_mem_jointsBetween_iff_of_lt {hi : i < F.length} (hpq : p < q) :
      F[i] ∈ F.jointsBetween p q d ↔ p ≤ i ∧ i < q ∧ i.bodd = (F.b != d) := by
  simp [getElem_mem_jointsBetween_iff, hpq.not_ge, _root_.and_assoc]

lemma getElem_mem_jointsBetween_iff_of_le {hi : i < F.length} (hpq : q ≤ p) :
      F[i] ∈ F.jointsBetween p q d ↔ (i < q ∨ p ≤ i) ∧ i.bodd = (F.b != d) := by
  simp only [getElem_mem_jointsBetween_iff, and_congr_left_iff]
  lia

@[simp]
lemma getElem_mem_joints_between_zero_length {hi : i < F.length} :
      F[i] ∈ F.jointsBetween 0 F.length d ↔ i.bodd = (F.b != d) := by
  simp [getElem_mem_jointsBetween_iff_of_lt (show 0 < F.length by grind), hi]

lemma bodd_of_mem_jointsBetween {_ : i < F.length} (hi : F[i] ∈ F.jointsBetween p q d) :
    i.bodd = (F.b != d) :=
  (getElem_mem_jointsBetween_iff.1 hi).2

lemma jointsBetween_congr {M' : Matroid α} {F' : M'.Fan} (hF : (F : List α) = (F' : List α))
    (hb : F.b = F'.b) : F.jointsBetween p q d = F'.jointsBetween p q d := by
  rw [jointsBetween, jointsBetween, hF, hb]

@[simp]
lemma jointsBetween_bDual (F : M.Fan) (d d' : Bool) :
    (F.bDual d).jointsBetween p q d' = F.jointsBetween p q (d != d') :=
  getElems_congr _ fun i hi ↦ by simp

@[simp]
lemma jointsBetween_dual (F : M.Fan) (d : Bool) :
    F.dual.jointsBetween p q d = F.jointsBetween p q !d :=
  getElems_congr _ fun i hi ↦ by simp

lemma jointsBetween_subset (F : M.Fan) (p q d) : F.jointsBetween p q d ⊆ F :=
  getElems_subset_toSet ..

lemma jointsBetween_subset_extract (hpq : p < q) :
    F.jointsBetween p q d ⊆ {x | x ∈ (F : List α).extract p q} := by
  rw [← getElems_Ico]
  exact getElems_mono _ <| by grind

lemma jointsBetween_subset_iff_of_lt (F : M.Fan) (hpq : p < q) : F.jointsBetween p q d ⊆ X ↔
    ∀ i (hi : i < F.length), p ≤ i → i < q → i.bodd = (F.b != d) → F[i] ∈ X := by
  simp [jointsBetween, hpq.not_ge, getElems_subset_iff]

lemma jointsBetween_reverse (hp : p ≤ F.length) (hq : q ≤ F.length) :
    F.reverse.jointsBetween p q d = F.jointsBetween (F.length - q) (F.length - p) d := by
  rw [jointsBetween, reverse_toList, getElems_reverse, jointsBetween, ← getElems_inter_Iio,
    eq_comm, ← getElems_inter_Iio]
  convert rfl using 2
  ext i
  simp [length_toList, reverse_left, preimage_ofPred_eq, Set.mem_inter_iff, mem_ofPred_eq,
    mem_Iio, tsub_le_iff_right, and_congr_left_iff]
  intro hi
  convert Iff.rfl using 2
  · grind
  rw [F.right_eq, Nat.sub_sub, Nat.bodd_sub (by lia), Nat.bodd_add]
  grind [cases Bool]

lemma jointsBetween_ofPair {e f he hf} {hef : e ≠ f} {b} :
    (ofPair (M := M) he hf hef b).jointsBetween 0 2 d = bif b == d then {e} else {f} := by
  rw [jointsBetween, ofPair_toList, getElems_cons]
  obtain rfl | rfl := b.eq_or_eq_not d
  · suffices ∀ a ∈ [f].getElems {x | x = 0 ∧ x.bodd = true}, a = e by simpa
    rintro a
    rw [getElems_congr (t := ∅) _ (by simp)]
    simp
  simp
  suffices [f].getElems {x | x = 0 ∧ x.bodd = false} = {f} by simpa
  rw [getElems_congr (t := {0}) _ (by simp), getElems_singleton (by simp), List.getElem_cons_zero]

lemma jointsBetween_eq_min_right (hp : p < F.length) (hpq : p < q) :
    F.jointsBetween p q d = F.jointsBetween p (min q F.length) d :=
  getElems_congr _ fun i hi ↦ by simp [hpq.not_ge, hp.not_ge, hi]

lemma jointsBetween_tail (hF : 3 ≤ F.length) {p q : ℕ} (hpq : p < q) (d : Bool) :
    (F.tail hF).jointsBetween p q d = F.jointsBetween (p + 1) (q + 1) d := by
  simp only [jointsBetween, tail_toList, hpq.not_ge, _root_.false_and, _root_.or_false, tail_left,
    not_bne, bnot_bne, getElems_tail, Order.add_one_le_iff, Order.lt_add_one_iff,
    add_le_add_iff_right]
  refine getElems_congr _ fun i hi ↦ ⟨?_, by cases i with simp⟩
  rintro ⟨i, ⟨hi', hi''⟩, rfl⟩
  simpa [hi']

lemma jointsBetween_add_one_self (F : M.Fan) (d : Bool) (hp : p < F.length) :
    F.jointsBetween p (p + 1) d = bif (p.bodd == (F.b != d)) then {F[p]} else ∅ := by
  obtain rfl | rfl := d.eq_or_eq_not (F.b == p.bodd)
  · rw [jointsBetween, getElems_congr (t := ∅)]
    · simp
    grind
  rw [jointsBetween, getElems_congr (t := {p}), getElems_singleton hp]
  · simp
  grind

lemma jointsBetween_dropLast (hF : 3 ≤ F.length) (d : Bool) (hpq : p < q) (hq : q < F.length) :
    (F.dropLast hF).jointsBetween p q d = F.jointsBetween p q d := by
  rw [jointsBetween, dropLast_toList, getElems_dropLast F.nodup (by simp), jointsBetween]
  simp only [dropLast_left, sdiff_eq_left, disjoint_singleton_right]
  rw [List.getLast_eq_getElem, F.nodup.getElem_mem_getElems_iff, length_toList, mem_ofPred_eq]
  lia

lemma jointsBetween_add_one_left_eq_self (hp : p.bodd = (F.b == d)) (hpq : q ≠ p + 1) :
    F.jointsBetween (p + 1) q d = F.jointsBetween p q d := by
  refine getElems_congr _ fun i hi ↦ ?_
  obtain rfl | hne := eq_or_ne i p
  · cases d with simp [hp]
  grind

lemma insert_jointsBetween_add_one_left (hp : p.bodd = (F.b != d)) (hpq : q ≠ p + 1)
    (hp : p < F.length) :
    insert F[p] (F.jointsBetween (p + 1) q d) = F.jointsBetween p q d := by
  rw [jointsBetween, ← getElem_toList, ← getElems_insert, jointsBetween]
  refine getElems_congr _ fun i hi ↦ ?_
  obtain rfl | hne := eq_or_ne i p <;>
  grind

lemma jointsBetween_add_one_left_eq_sdiff (hpq : q ≠ p + 1) (hp : p < F.length) :
    (F.jointsBetween (p + 1) q d) = (F.jointsBetween p q d) \ {F[p]} := by
  obtain h | h := p.bodd.eq_or_eq_not (F.b != d)
  · rw [← insert_jointsBetween_add_one_left h hpq hp, insert_sdiff_self_of_notMem]
    have hrw : q ≤ p + 1 → q ≤ p := by lia
    simpa [getElem_mem_jointsBetween_iff, h]
  rw [jointsBetween_add_one_left_eq_self (by simp [h]) (by simpa), sdiff_singleton_eq_self]
  cases d with simp [getElem_mem_jointsBetween_iff, h]

lemma jointsBetween_add_one_right_eq_self (hq : q.bodd = (F.b == d)) (hpq : p ≠ q) :
    F.jointsBetween p (q + 1) d = F.jointsBetween p q d := by
  refine getElems_congr _ fun i hi ↦ ?_
  obtain rfl | hne := eq_or_ne i q
  · cases d with simp [hq]
  grind

lemma jointsBetween_add_one_right_eq_insert (hq : q.bodd = (F.b != d)) (hpq : p ≠ q)
    (hqF : q < F.length) :
    F.jointsBetween p (q + 1) d = insert F[q] (F.jointsBetween p q d) := by
  rw [eq_comm, jointsBetween, ← getElem_toList, ← getElems_insert]
  refine getElems_congr _ fun i hi ↦ ?_
  obtain rfl | hne := eq_or_ne i q
  · simp [hq, le_or_gt]
  grind

lemma jointsBetween_add_two_right (hpq : p < q) (hq : q + 1 < F.length) :
    F.jointsBetween p (q + 2) d = insert (bif q.bodd == (F.b == d) then F[q + 1] else F[q])
      (F.jointsBetween p q d) := by
  obtain hqb | hqb := q.bodd.eq_or_eq_not (F.b == d)
  · rw [← one_add_one_eq_two, ← add_assoc, cond_pos (by simpa),
      jointsBetween_add_one_right_eq_insert (by simpa) (by lia),
      jointsBetween_add_one_right_eq_self hqb (by lia)]
  rw [← one_add_one_eq_two, ← add_assoc, cond_neg (by cases d with simp [hqb]),
    jointsBetween_add_one_right_eq_self (by simpa) (by lia),
    jointsBetween_add_one_right_eq_insert (by simpa) (by lia)]

lemma jointsBetween_add_one_right_sdiff (hpq : p ≠ q) (hqF : q < F.length) :
    (F.jointsBetween p (q + 1) d) \ {F[q]} = F.jointsBetween p q d := by
  obtain h | h := q.bodd.eq_or_eq_not (F.b == d)
  · rw [jointsBetween_add_one_right_eq_self h hpq, sdiff_singleton_eq_self]
    cases d with simp [getElem_mem_jointsBetween_iff, h]
  rw [jointsBetween_add_one_right_eq_insert (by simp [h]) hpq hqF, insert_sdiff_self_of_notMem]
  simp [getElem_mem_jointsBetween_iff, h, le_iff_lt_or_eq, hpq]

lemma jointsBetween_add_two_self (F : M.Fan) (d : Bool) (hp : p + 1 < F.length) :
    F.jointsBetween p (p + 2) d = {F[p + (p.bodd == (F.b == d)).toNat]} := by
  obtain rfl | rfl := d.eq_or_eq_not (F.b == p.bodd)
  · rw [← one_add_one_eq_two, ← add_assoc, jointsBetween_add_one_right_eq_insert (by simp)
      (by simp) hp, jointsBetween_add_one_self _ _ (by lia), cond_neg (by simp)]
    simp
  rw [← one_add_one_eq_two, ← add_assoc, jointsBetween_add_one_right_eq_self (by simp) (by simp),
    jointsBetween_add_one_self _ _ (by lia)]
  simp

lemma jointsBetween_mono {p' q'} (hpq : p < q) (hp' : p' ≤ p) (hq' : q ≤ q') :
    F.jointsBetween p q d ⊆ F.jointsBetween p' q' d := by
  refine getElems_mono _ ?_
  simp only [hpq.not_ge, show ¬(q' ≤ p') by lia, ofPred_subset_ofPred]
  lia

lemma jointsBetween_encard_add_eq (d) (hpq : p < q) (hq : q ≤ F.length) :
    2 * (F.jointsBetween p q d).encard + p + (d == (F.b == p.bodd)).toNat
      = q + (d == (F.b == q.bodd)).toNat := by
  induction q using Nat.strong_induction_on with | h q ih =>
  obtain rfl | hne := eq_or_ne q (p + 1)
  · rw [jointsBetween_add_one_self _ _ (by lia)]
    obtain rfl | rfl := d.eq_or_eq_not (F.b == p.bodd)
    · cases h : p.bodd with simp [h]
    cases h : F.b with simp [add_assoc, add_comm (2 : ℕ∞), one_add_one_eq_two]
  obtain rfl | hne' := eq_or_ne q (p + 2)
  · rw [jointsBetween_add_two_self _ _ (by lia), encard_singleton]
    simp [add_comm (2 : ℕ∞)]
  obtain ⟨q, hpq', rfl⟩ : ∃ q', p < q' ∧ q = q' + 2 := ⟨q - 2, by grind⟩
  rw [jointsBetween_add_two_right hpq' (by lia), encard_insert_of_notMem, mul_add,
    add_assoc, add_right_comm, ← add_assoc, ih _ (by lia) hpq' (by lia), add_right_comm]
  · simp
  simp [Bool.apply_cond, getElem_mem_jointsBetween_iff_of_lt hpq']

lemma jointsBetween_encard_add_of_bodd_eq (hpq : p < q) (hq : q ≤ F.length)
    (hpb : p.bodd = q.bodd) : 2 * (F.jointsBetween p q d).encard + p = q := by
  simpa [hpb] using F.jointsBetween_encard_add_eq d hpq hq

lemma getElems_Ico_subset_closure_jointsBetween (F : M.Fan) (hp : p.bodd = F.b) (hq : q.bodd = !F.b)
    (hqF : q ≤ F.length) (hpq : p < q) : {e | e ∈ (F : List α).extract p q} ⊆
      M.closure (F.jointsBetween p q false) := by
  simp only [extract_eq_take_drop, mem_extract_iff_getElem, getElem_toList', length_toList,
    exists_and_left, Set.subset_def, mem_ofPred_eq, forall_exists_index, and_imp]
  rintro _ i hpi hiq hlt rfl
  obtain hb | hb := F.b.eq_or_eq_not i.bodd
  · exact mem_closure_of_mem' _ <| by simp [getElem_mem_jointsBetween_iff_of_lt hpq, hpi, hiq, hb]
  obtain rfl | i := i
  · grind
  obtain rfl | hlt := hpi.eq_or_lt
  · simp [hb] at hp
  simp only [Nat.bodd_succ, Bool.not_not] at hb
  have hiq : i + 2 ≠ q := by
    rintro rfl
    simp [hb] at hq
  refine mem_of_mem_of_subset (F.isTriangle_of_eq i (by lia) (by simp [hb])).mem_closure₂ <|
    closure_subset_closure _ ?_
  grind [pair_subset_iff, getElem_mem_jointsBetween_iff_of_lt hpq, Nat.bodd_succ]

lemma joints_indep (F : M.Fan) (h_pair : F.b = false → F.c = false → ¬ M.Parallel F[0] F.getLast) :
    M.Indep (F.jointsBetween 0 F.length false) := by
  induction hn : F.length using Nat.strong_induction_on generalizing F M with | h n ih =>
  wlog h : F.b = false → F.c = false generalizing F with aux
  · simp only [Classical.not_imp, not_eq_false] at h
    convert aux F.reverse (fun hb hc h ↦ h_pair hc hb <| by simpa using h.symm) (by simpa)
      (by simp [h.1]) using 1
    rw [jointsBetween_reverse (by simp) hn.ge, hn, Nat.sub_self, Nat.sub_zero]
  by_cases h2 : F.length ≤ 2
  · obtain ⟨e, f, b, he, hf, hef, rfl⟩ := eq_of_length_le_two h2
    rw [← hn, length_ofPair, jointsBetween_ofPair]
    cases b with
    | false => simpa using he false
    | true => simpa using hf false
  cases hb : F.b
  · specialize ih (F.length - 1) (by lia) (F.contractHead (by lia) (by simp [hb]) h_pair)
      (by simp [hb]) (by simp [length_tail])
    rw [jointsBetween_congr (F' := F.tail (by lia)) (by simp) (by simp),
      jointsBetween_tail _ (by lia), F.isNonloop.contractElem_indep_iff,
      insert_jointsBetween_add_one_left (by simpa) (by lia), Nat.sub_add_cancel (by lia), hn] at ih
    exact ih.2
  have hpara : F.c = false → ¬ M.Parallel F[1] F.getLast := by
    intro hc hpara
    have hlen : 1 = F.length ∨ 2 = F.length ∨ 3 = F.length := by
      simpa using (F.isTriangle_bDual_of_eq 0 true (by lia)
        (by simp [hb])).isCircuit.mem_iff_mem_of_parallel_bDual hpara
    have hcon := (show F.length = 3 by lia) ▸ F.length_bodd_eq_false (by simp [hb, hc])
    simp at hcon
  have hwin := ih (F.tail (by lia)).length (by grind) (F.tail (by lia)) (by simpa [hb]) rfl
  rwa [jointsBetween_tail (by grind) (by grind), length_tail_add_one,
    jointsBetween_add_one_left_eq_self (by simp [hb]) (by grind), hn] at hwin

lemma indep_of_subset_joints (F : M.Fan) {I} (hI : I ⊆ F.jointsBetween 0 F.length false)
    (hpq : F.b = false → F.c = false → F[0] ∈ I → F.getLast ∈ I → ¬ M.Parallel F[0] F.getLast) :
    M.Indep I := by
  have hle := F.length_ge_two
  by_cases! hdg : F.b = false → F.c = false → ¬ M.Parallel F[0] F.getLast
  · exact (F.joints_indep hdg).subset hI
  obtain ⟨hb, hc, hpara⟩ := hdg
  obtain h0 | hlast : F[0] ∉ I ∨ F.getLast ∉ I := by tauto
  · refine ((F.tail (by grind)).joints_indep (by simp [hb])).subset ?_
    rwa [jointsBetween_tail _ (by grind), length_tail_add_one,
      jointsBetween_add_one_left_eq_sdiff (by grind) (by grind), subset_sdiff_singleton_iff,
      and_iff_left h0]
  refine ((F.dropLast (by grind)).joints_indep (by simp [hc])).subset ?_
  rwa [jointsBetween_dropLast _ _ (by grind) (by grind), length_dropLast,
    ← jointsBetween_add_one_right_sdiff (by lia) (by lia), Nat.sub_add_cancel (by lia),
    subset_sdiff_singleton_iff, ← getLast_eq_getElem, and_iff_left hlast]

lemma jointsBetween_indep (F : M.Fan) (hp : p < F.length) (hlt : p < q)
    (hpq : p = 0 → F.length ≤ q → F.b = false → F.c = false →
      ¬ M.Parallel F[0] F.getLast) : M.Indep (F.jointsBetween p q false) := by
  wlog hq : q ≤ F.length generalizing q with aux
  · rw [jointsBetween_eq_min_right hp hlt]
    exact aux (by lia) (by simpa) (by simp)
  refine F.indep_of_subset_joints (jointsBetween_mono hlt (by simp) hq) ?_
  refine fun hb hc h0 hlast ↦ hpq ?_ ?_ hb hc
  · simp only [getElem_mem_jointsBetween_iff_of_lt hlt, nonpos_iff_eq_zero] at h0
    exact h0.1
  simp only [getLast_eq_getElem, getElem_mem_jointsBetween_iff_of_lt hlt, bne_false] at hlast
  lia

lemma eRk_le (F : M.Fan) : 2 * M.eRk F ≤ F.length + 1 + F.b.toNat + F.c.toNat := by
  induction F using Fan.induction with
  | pair e f b he hf hef =>
    suffices 2 * M.eRk {e, f} ≤ 4 by
      simpa [add_assoc, ← Nat.cast_add, Bool.toNat_add_toNat_bnot]
    grw [eRk_le_encard, encard_pair_le, show (2 : ℕ∞) * 2 = 4 from rfl]
  | cons F₀ e heF₀ hT ih =>
    simp only [cons_toSet, cons_length, Nat.cast_add, Nat.cast_one]
    cases hb : F₀.b
    · grw [eRk_insert_le_add_one, mul_add, ih, hb, toNat_false]
      simp only [Nat.cast_zero, add_zero, mul_one, cons_left, hb, Bool.not_false, toNat_true,
        Nat.cast_one, cons_right]
      enat_to_nat!; lia
    grw [eRk_insert_of_mem_closure, cons_left, cons_right, ih, hb, Bool.not_true, toNat_false,
      Nat.cast_zero, add_zero, toNat_true, Nat.cast_one]
    rw [hb, Bool.not_true, Matroid.bDual_false] at hT
    exact mem_of_mem_of_subset hT.mem_closure₁ <| M.closure_subset_closure <| by simp [pair_subset]

lemma eRk_eq (F : M.Fan) (hF : F.length.bodd = true)
    (hpara : ¬ (M.bDual F.b).Parallel F[0] F.getLast) : 2 * (M.bDual F.b).eRk F = F.length + 1 := by
  nth_grw 1 [le_antisymm_iff, ← F.bDual_toSet F.b, (F.bDual F.b).eRk_le,
    and_iff_right (by simp [F.right_eq_left hF])]
  grw [← F.bDual_toSet (d := F.b),
    ← (F.bDual F.b).jointsBetween_subset 0 (F.bDual F.b).length false, Indep.eRk_eq_encard
    (by simpa using (F.bDual F.b).joints_indep (fun _ _ ↦ by simpa))]
  simp only [bDual_length, jointsBetween_bDual, bne_false]
  have hlen := F.jointsBetween_encard_add_eq F.b (p := 0) (q := F.length) (by grind) (by lia)
  simp only [Nat.cast_zero, add_zero, Nat.bodd_zero, beq_false, beq_not_self, toNat_false,
    beq_self_left, hF, toNat_true, Nat.cast_one] at hlen
  exact hlen.ge


/-- Let `F[p]` and `F[q]` be joints of a fan, and `K` be the set of cojoints between `p` and `q`.
If `F[p]` and `F[q]` are not parallel and at the beginning and the end of the fan,
then `{F[p], F[q]} ∪ K` is a circuit.

The nondegeracy hypothesis has some redundancy, since `i = 0` and `q + 1 = F.length` implies that
`F.b = F.c = false`; we include it so it is easier to discharge quickly in various cases.  -/
lemma isCircuit_interval (F : M.Fan) (p q : ℕ) (hpq : p < q) (hqF : q < F.length)
    (hpb : p.bodd = F.b) (hqb : q.bodd = F.b)
    (hdg : F.b = false → F.c = false → p = 0 → q + 1 = F.length → ¬ M.Parallel F[0] F.getLast) :
    M.IsCircuit <| (insert F[p] (insert F[q] (F.jointsBetween p q true))) := by
  induction q using Nat.strong_induction_on with | h q ih =>
  obtain rfl | hpq1 := eq_or_ne q (p + 1)
  · simp [hpb] at hqb
  obtain rfl | hpq2 := eq_or_ne q (p + 2)
  · rw [jointsBetween_add_two_self _ _ (by lia), pair_comm]
    simpa [hpb] using (F.isTriangle_of_eq p (by lia) hpb).isCircuit
  obtain ⟨q, hq', hqb, rfl⟩ : ∃ q', p < q' ∧ q = q' + 2 := ⟨q - 2, by lia⟩
  simp only [Nat.bodd_succ, Bool.not_not] at hqb
  have hC := ih q (by lia) hq' (by lia) hqb (by grind)
  have hT := F.isTriangle_of_eq q (by lia) hqb
  have hcl : F[q + 2] ∉ M.closure (insert F[p] (insert F[q] (F.jointsBetween p q true))) := by
    grw [jointsBetween_subset_extract hq', ← toSet_concat_eq, ← F.getElem_toList,
      ← F.getElem_toList, ← extract_add_one_right _ hq'.le, insert_eq_of_mem,
      F.getElems_Ico_subset_closure_jointsBetween hpb (by simpa) (by lia) (by lia),
        closure_closure]
    · have hi := F.jointsBetween_indep (p := p) (q := q + 3) (by lia) (by lia) (by grind)
      have hnm : F[q + 2] ∈ F.jointsBetween p (q + 3) false := by
        simpa [getElem_mem_jointsBetween_iff_of_lt (show p < q + 3 by lia), hpq.le]
      refine notMem_subset (closure_mono _ ?_) (hi.notMem_closure_sdiff_of_mem hnm)
      rw [subset_sdiff_singleton_iff, and_iff_right (jointsBetween_mono (by lia) (by lia) (by lia))]
      simp [getElem_mem_jointsBetween_iff_of_lt (show p < q + 1 by lia)]
    exact F.nodup.getElem_mem_extract_iff.2 <| by lia
  have hC' := hT.swap_right.union_diff_singleton_isCircuit hC (by simp) hcl
  rw [insert_sdiff_singleton_comm (by simp), insert_sdiff_of_notMem _ (by simp),
    insert_sdiff_of_notMem _ (by simp [hq'.ne]), insert_sdiff_self_of_notMem
    (by simp [getElem_mem_jointsBetween_iff_of_lt hq'])] at hC'
  rwa [jointsBetween_add_two_right hq' (by lia), cond_pos (by simpa using hqb),
    insert_comm, insert_comm F[p]]


/-- If a circuit of a matroid contains joints `F[p + 1], F[q]` of a fan `F`,
and does not contain the cojoint `F[p]`,
then it comprises precisely `F[p + 1], F[q]`, and the cojoints between them.  -/
lemma eq_interval_of_notMem_mem_mem (F : M.Fan) (hpq : p + 1 < q)
    (hqF : q < F.length) (hpb : p.bodd = !F.b) (hqb : q.bodd = F.b) (hC : M.IsCircuit C)
    (hpC : F[p] ∉ C) (hp1C : F[p + 1] ∈ C) (hqC : F[q] ∈ C) :
    C = insert F[p + 1] (insert F[q] <| F.jointsBetween (p + 1) q true) := by
  induction q using Nat.strong_induction_on with | h q ih =>
  suffices aux : F.jointsBetween (p + 1) q true ⊆ C from
    hC.eq_of_superset_isCircuit (F.isCircuit_interval _ q hpq hqF (by simpa) hqb (by simp)) <|
      insert_subset hp1C (insert_subset hqC aux)
  rw [jointsBetween_subset_iff_of_lt _ hpq]
  intro i hi hpi hiq hib
  simp only [bne_true] at hib
  induction i using Nat.strong_induction_on with | h i ih' =>
  obtain rfl | rfl | ⟨i, rfl, hpi''⟩ : i = p + 1 ∨ i = p + 2 ∨ ∃ i', i' + 2 = i ∧ p + 1 ≤ i' := by
    obtain rfl | rfl | i := i <;> grind
  · simp [hpb] at hib
  · rwa [← (F.isTriangle_bDual_of_eq p true (by lia)
        (by simp [hpb])).mem_iff_mem_of_isCircuit_bDual hC hpC]
  simp only [Nat.bodd_succ, Bool.not_not] at hib
  by_cases hi1C : F[i + 1] ∈ C
  · obtain rfl := ih (i + 1) (by lia) (by lia) (by lia) (by simpa using hib) hpC hp1C hi1C
    simp only [Set.mem_insert_iff, getElem_inj, show q ≠ p + 1 by lia, show q ≠ i + 1 by lia,
      _root_.false_or] at hqC
    rw [getElem_mem_jointsBetween_iff_of_lt (by lia)] at hqC
    lia
  rw [← (F.isTriangle_bDual_of_eq i true (by lia)
    (by simp [hib])).swap_left.mem_iff_mem_of_isCircuit_bDual hC hi1C]
  exact ih' i (by lia) (by lia) (by lia) (by lia) hib

/-- If a circuit contains a joint `F[p + 1]`, but not the cojoint before it, and does not contain
some cojoint `F[q]` after `p`, then the circuit is an interval. -/
lemma exists_eq_interval_of_notMem_mem_add_one (F : M.Fan) (hpq : p + 1 < q)
    (hqF : q < F.length) (hpb : p.bodd = !F.b) (hqb : q.bodd = !F.b) (hC : M.IsCircuit C)
    (hpC : F[p] ∉ C) (hp1C : F[p + 1] ∈ C) (hqC : F[q] ∉ C) :
    ∃ (r : ℕ) (_ : p + 1 < r) (_ : r < q), r.bodd = F.b ∧
    C = insert F[p + 1] (insert F[r] (F.jointsBetween (p + 1) r true)) := by
  by_cases! hr : ∃ (r : ℕ) (hpr : p + 1 < r) (hrq : r < q), r.bodd = F.b ∧ F[r] ∈ C
  · obtain ⟨r, hpr, hrq, hrb, hrC⟩ := hr
    exact ⟨r, hpr, hrq, hrb, eq_interval_of_notMem_mem_mem _ hpr _ hpb hrb hC hpC hp1C hrC⟩
  suffices aux : ∀ i (hi : i < F.length), p < i → i ≤ q → i.bodd = !F.b → F[i] ∈ C by
    exact False.elim <| hqC <| aux q hqF (by lia) rfl.le hqb
  intro i hi hpi hiq hib
  induction i using Nat.strong_induction_on with | h i ih =>
  obtain rfl | rfl | ⟨i, rfl, hpi''⟩ : i = p + 1 ∨ i = p + 2 ∨ ∃ i', i' + 2 = i ∧ p + 1 ≤ i' := by
    obtain rfl | rfl | i := i <;> grind
  · simp [hpb] at hib
  · rwa [← (F.isTriangle_bDual_of_eq p true (by lia)
      (by simp [hpb])).mem_iff_mem_of_isCircuit_bDual hC hpC]
  simp only [Nat.bodd_succ, Bool.not_not] at hib
  rw [← (F.isTriangle_bDual_of_eq i true (by lia)
    (by simp [hib])).swap_left.mem_iff_mem_of_isCircuit_bDual hC]
  · grind
  exact hr _ (by lia) (by lia) (by simpa)

/-- If a circuit doesn't contain two particular cojoints `F[s], F[t]` of a fan `F`,
but it contains something between them, then it is an interval. -/
lemma exists_eq_interval_of_notMem_mem_notMem {s t r : ℕ} (F : M.Fan) (hsr : s < r)
    (hrt : r < t) (ht : t < F.length) (hsb : s.bodd = !F.b) (htb : t.bodd = !F.b)
    (hC : M.IsCircuit C) (hsC : F[s] ∉ C) (hrC : F[r] ∈ C) (htC : F[t] ∉ C) :
    ∃ (p q : ℕ) (_ : s < p) (_ : p < q) (_ : q < t), p.bodd = F.b ∧ q.bodd = F.b ∧
    C = insert F[p] (insert F[q] (F.jointsBetween p q true)) := by
  induction h : r - s using Nat.strong_induction_on generalizing r s with | h d ih =>
  by_cases hs1 : F[s + 1] ∈ C
  · obtain ⟨j, hsj, hjt, hjb, rfl⟩ :=
      F.exists_eq_interval_of_notMem_mem_add_one (by lia) ht hsb htb hC hsC hs1 htC
    exact ⟨s + 1, j, by simp [hsb, hsj, hjt, hjb]⟩
  have hs1i : s + 1 < r := by grind
  rw [(F.isTriangle_bDual_of_eq s true
    (by lia) (by simp [hsb])).mem_iff_mem_of_isCircuit_bDual hC hsC] at hs1
  obtain ⟨p, q, hpq⟩ := ih (r - (s + 2)) (by lia) (by grind) hrt (by simpa) hs1 hrC rfl
  exact ⟨p, q, by grind⟩

/-- A parallel pair in a fan is hard to find; it must either comprise both ends, or two consecutive
elements at one of the ends. The upper bound of 6 is best-possible,
since the `5`-fan `[0, 1, 2, 3, 4]` can have the pairs `[0, 2]` and `[1, 3]` both parallel. -/
lemma eq_eq_of_parallel (F : M.Fan) (hF : 6 ≤ F.length) {hi : i < F.length}
    {hj : j < F.length} (hij : i < j) (hpara : M.Parallel F[i] F[j]) :
    (F.b = true ∧ i = 0 ∧ j = 1) ∨ (F.c = true ∧ i + 2 = F.length ∧ j + 1 = F.length) ∨
    F.b = false ∧ F.c = false ∧ i = 0 ∧ j + 1 = F.length := by
  replace hC := hpara.isCircuit_of_ne (by grind)
  obtain ⟨rfl | rfl | d, rfl⟩ := Nat.exists_eq_add_of_lt hij
  · obtain rfl | i := i
    · cases hb : F.b
      · simpa using (F.isTriangle_of_eq 0 (by lia) hb.symm).notMem_of_mem_of_parallel hpara
      simp
    obtain hib | hib := i.bodd.eq_or_eq_not F.b
    · simpa using (F.isTriangle_of_eq i (by lia) hib).notMem_of_mem_of_parallel hpara
    by_cases hle : i + 3 < F.length
    · simpa using (F.isTriangle_of_eq (i + 1) (by lia) (by simpa)).notMem_of_mem_of_parallel hpara
    simp [F.right_eq, show F.length = i + 3 by lia, hib]
  · obtain hib | hib := i.bodd.eq_or_eq_not F.b
    · simpa [add_assoc] using (F.isTriangle_of_eq i (by lia) hib).notMem_of_mem_of_parallel hpara
    by_cases! h2i : i < 2
    · simpa [add_assoc] using (F.isTriangle_bDual_of_eq (i + 2) true (by lia)
        (by simp [hib])).isCircuit.mem_iff_mem_of_parallel_bDual hpara
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' h2i
    have hcon := (F.isTriangle_bDual_of_eq i true (by lia) (by
      simp [show i.bodd = !F.b by simpa using hib])).isCircuit.mem_iff_mem_of_parallel_bDual hpara
    simp [add_assoc] at hcon
  obtain rfl | i := i
  · cases hb : F.b
    · cases hdb : d.bodd
      · simpa using (F.isTriangle_bDual_of_eq (d + 1) true (by lia)
          (by simp [hb, hdb])).mem_iff_mem_of_isCircuit_bDual hC
      obtain h_eq | hne := eq_or_ne (d + 4) F.length
      · simpa [← h_eq, F.right_eq, hdb]
      have hwin := (F.isTriangle_bDual_of_eq (d + 2) true (by lia)
        (by simp [hdb, hb])).isCircuit.mem_iff_mem_of_parallel_bDual hpara
      simp at hwin
    simpa using (F.isTriangle_bDual_of_eq 0 true (by lia)
      (by simpa)).isCircuit.mem_iff_mem_of_parallel_bDual hpara
  exfalso
  simp only [add_assoc, add_comm 1, Nat.reduceAdd] at hC
  obtain hib | hib := i.bodd.eq_or_eq_not F.b
  · simpa [add_assoc i, ← add_assoc 1] using (F.isTriangle_bDual_of_eq (i + 1) true (by lia)
      (by simp [hib])).isCircuit.mem_iff_mem_of_parallel_bDual hpara
  have hwin := (F.isTriangle_bDual_of_eq i true (by lia)
    (by simp [hib])).isCircuit.mem_iff_mem_of_parallel_bDual hpara
  simp [add_assoc i] at hwin

@[grind .]
lemma length_ge_four_of_eq_ground [M.Simple] [M✶.Simple] (F : M.Fan)
    (hFE : (F : Set α) = M.E) : 4 ≤ F.length := by
  have hF2 := F.length_ge_two
  have hr := M.eRk_pair_eq (e := F[0]) (f := F[1]) (by simp) (by simp) (by simp)
  have hr1 := M✶.eRk_pair_eq (e := F[0]) (f := F[1]) (by simp) (by simp) (by simp)
  have hle := encard_le_encard hFE.symm.subset
  grw [← eRank_add_eRank_dual, ← M.eRk_le_eRank {F[0], F[1]},
    ← M✶.eRk_le_eRank {F[0], F[1]}, hr, hr1, F.encard_toSet_eq,
    show (2 : ℕ∞) + 2 = 4 from rfl, Nat.ofNat_le_cast] at hle
  assumption

lemma eConn_le_two (F : M.Fan) : M.eConn F ≤ 2 := by
  grw [← ENat.add_le_add_iff_right (k := F.length) (by simp), ← F.encard_toSet_eq,
    ← eRk_add_eRk_dual_eq _ _ F.subset_ground,
    ← ENat.mul_le_mul_left_iff (a := 2) (by simp) (by simp), mul_add, F.eRk_le,
    show M✶.eRk F = M✶.eRk F.dual by simp, F.dual.eRk_le]
  simp only [dual_length, dual_left, dual_right, encard_toSet_eq]
  have h1 := F.b.toNat_add_toNat_bnot
  have h2 := F.c.toNat_add_toNat_bnot
  enat_to_nat!; lia

/-- If the head is spanned by the tail in the appropriate dual of `b`, then the fan
has connectivity one. -/
lemma eConn_le_one_of_mem_closure (F : M.Fan)
    (hcl : F[0] ∈ (M.bDual (!F.b)).closure {e | e ∈ (F : List α).tail}) : M.eConn F ≤ 1 := by
  induction F using Fan.induction with
  | pair e f b he hf hef =>
    grw [toSet_ofPair, ← eConn_bDual M (!b), eConn_le_eRk, eRk_insert_of_mem_closure,
      eRk_le_encard, encard_singleton]
    simpa [getElem_ofPair] using hcl
  | cons F₀ e heF₀ hT ih =>
    grw [cons_toSet, ← ENat.add_one_le_add_one_iff, ← eConn_bDual M (F₀.b),
      eConn_insert_add_one_eq (by simpa using hcl) _ (by simpa), ← bDual_toSet F₀ (F₀.b),
      eConn_le_two, one_add_one_eq_two]
    simp only [dual_bDual]
    exact mem_of_mem_of_subset hT.mem_closure₁ <| closure_subset_closure _ <|
      by simp [pair_subset_iff]

/-- TODO : I think this should hold even if the fan has odd length. -/
lemma IsFan.eConn_eq_zero_of_mem_closure_mem_closure (h : M.IsFan F b (!b))
    (hcl : F[0] ∈ (M.bDual (!b)).closure {x | x ∈ F.tail})
    (hcl' : F[F.length - 1] ∈ (M.bDual b).closure {x | x ∈ F.dropLast}) :
    M.eConn {e | e ∈ F} = 0 := by
  wlog hb : b = false generalizing F b with aux
  · obtain rfl : b = true := by simpa using hb
    simpa using aux (F := F.reverse) (b := false) (by simpa using h.reverse) (by simpa using hcl')
      (by simpa using hcl) rfl
  subst hb
  have hr := (M.eRk_add_eRk_dual_eq {e | e ∈ F} h.subset_ground).ge
  replace hcl' := eRk_insert_of_mem_closure hcl'
  rw [← toSet_concat_eq, ← getLast_eq_getElem h.ne_nil, dropLast_concat_getLast, bDual_false]
    at hcl'
  replace hcl := eRk_insert_of_mem_closure hcl
  rw [← toSet_cons_eq, getElem_zero, cons_head_tail, Bool.not_false, bDual_true] at hcl
  grw [← ENat.mul_le_mul_left_iff (a := 2) (by simp) (by simp), mul_add, mul_add, hcl, hcl',
    h.nodup.encard_toSet_eq] at hr
  obtain h2 | h3 := le_or_gt F.length 2
  · grw [eRk_le_encard, eRk_le_encard, encard_toSet_le, encard_toSet_le] at hr
    simp only [length_dropLast, ENat.natCast_sub, Nat.cast_one, length_tail] at hr
    enat_to_nat! <;> lia
  grw [(h.tail (by lia)).dual.eRk_le (by grind [h.length_even]),
    (h.dropLast (by lia)).eRk_le (by grind [h.length_even])] at hr
  simp only [length_dropLast, ENat.natCast_sub, Nat.cast_one, Bool.toNat_false,
    Bool.not_false, Bool.not_true, length_tail] at hr
  enat_to_nat! <;> lia


#exit



-- lemma joints_extract_indep (F : M.Fan)
--     (hpq : p = 0 → (F.joints false).length ≤ q → F.b = false → F.c = false →
--       ¬ M.Parallel F[0] F.getLast) : M.Indep {e | e ∈ (F.joints false).extract p q} := by
--   refine F.indep_of_subset_joints (extract_isInfix ..).subset fun hb hc h1 h2 ↦ hpq ?_ ?_ hb hc
--   · by_contra hcon
--     simp [mem_extract_iff_getElem, joints_getElem, hb, hcon] at h1
--   simp only [extract_eq_take_drop, mem_extract_iff_getElem, joints_getElem, hb, bne_self_eq_false,
--     toNat_false, mem_ofPred_eq, getElem_eq_getLast_iff] at h2
--   grind




-- /-- If `F` is a fan whose ends are joints, and `C` is a circuit containing the first but not
-- the second element of `F`, then `M` has a circuit containing the first element of `F`,
-- and no other elements of `F` except possibly the last.  -/
-- lemma IsFan.exists_isCircuit_subset_first_last (F : M.Fan false false)
--     (hC : M.IsCircuit C) (h0C : F[0] ∈ C) (h1C : F[1] ∉ C) :
--     ∃ C₀ ⊆ insert F[F.length - 1] C, M.IsCircuit C₀ ∧ F[0] ∈ C₀ := by
--   obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hF.two_le_length
--   suffices aux : ∀ k ≤ n, ∃ C₀, M.IsCircuit C₀ ∧ F[0] ∈ C₀ ∧ C₀ ⊆ C ∪ {e | e ∈ F} ∧
--       ∀ i (hi : i + 1 < F.length), F[i + 1] ∈ C₀ → k ≤ i by
--     refine Exists.imp ?_ <| aux n rfl.le
--     simp only [and_imp]
--     refine fun C₀ hC₀ h0C₀ hC₀ss h ↦ ⟨?_, hC₀, h0C₀⟩
--     refine fun e heC₀ ↦ ?_
--     by_cases heC : e ∈ C
--     · exact .inr heC
--     obtain ⟨rfl | i, hi, rfl⟩ := getElem_of_mem (show e ∈ F by grind)
--     · grind
--     obtain rfl : n = i := by grind
--     simp [hn, add_comm]
--   rintro (rfl | k) hk
--   · use C; grind
--   induction k with
--   | zero => use C; grind
--   | succ k ih =>
--     obtain ⟨C₀', hC₀', h0C₀', hC₀'ss, hClt⟩ := ih (by lia)
--     obtain hkC | hkC := em' (F[k + 2] ∈ C₀')
--     · exact ⟨C₀', by grind⟩
--     cases hb : !k.bodd
--     · have hT' := (hF.isTriad_getElem_of_eq k (by lia) (by simpa using hb)).reverse
--       obtain h1 | h2 := hT'.mem_or_mem_of_isCocircuit (K := C₀') (by simpa) hkC
--       · grind [hClt _ _ h1]
--       obtain rfl | k := k
--       · grind
--       grind [hClt _ _ h2]
--     obtain rfl | hlt := hk.eq_or_lt
--     · simpa [hn, ← hb] using hF.length_bodd_eq
--     have hT := hF.isTriangle_getElem_of_eq (k + 2) (by lia) (by simpa using hb)
--     have elim := hC₀'.strong_elimination hT.isCircuit (e := F[k + 2]) (f := F[0]) hkC (by simp)
--       h0C₀' (by simp [hF.nodup.getElem_inj_iff])
--     obtain ⟨C₀, hC₀ss, hC₀, h0C₀⟩ := elim
--     refine ⟨C₀, hC₀, h0C₀, ?_, fun i hi hiC₀ ↦ by grind [hF.nodup.getElem_inj_iff]⟩
--     grw [hC₀ss, hC₀'ss, sdiff_subset]
--     grind [Set.union_subset_iff, insert_subset_iff]

-- /-- For any fan `F = [a, b, ..., z]` whose ends are joints and for which `{a, b}` isn't series,
-- there is a circuit `C` with `a ∈ C ∩ F ⊆ {a, z}`. -/
-- lemma IsFan.exists_isCircuit_first_mem_of_length_odd (F : M.Fan false c)
--     (h_odd : Odd F.length) (h01 : ¬ M✶.Parallel (F[0]'(by grind)) (F[1]'hF.two_le_length)) :
--     ∃ C, M.IsCircuit C ∧ F[0] ∈ C ∧ ∀ i (hi : i + 1 < F.length),
--       F[i + 1] ∈ C → i + 2 = F.length := by
--   obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hF.two_le_length
--   suffices aux : ∀ k ≤ n, ∃ C, M.IsCircuit C ∧ F[0] ∈ C ∧
--       ∀ i (hi : i + 1 < F.length), F[i + 1] ∈ C → k ≤ i from
--     Exists.imp (by grind) <| aux n rfl.le
--   rw [parallel_dual_iff_forall_circuit (hF.dual.isNonloop (by simp)) hF.get_mem_ground] at h01
--   simp_rw [not_forall, exists_prop] at h01
--   intro k hk
--   induction k with
--   | zero => exact Exists.imp (by grind) h01
--   | succ k ih =>
--     obtain rfl | k := k
--     · exact Exists.imp (by grind) h01
--     obtain ⟨C, hC, h0C, hClt⟩ := ih (by lia)
--     obtain hkC | hkC := em' (F[k + 2] ∈ C)
--     · exact ⟨C, by grind⟩
--     by_cases hb : k.bodd = true
--     · obtain hwin | hwin := (hF.isTriangle_getElem k (by lia)).reverse.mem_or_mem_of_isCircuit_bDual
--         (by simpa [hb]) hkC
--       · grind
--       obtain rfl | k := k; simp at hb
--       grind
--     have hnk : n ≠ k + 2 := fun hnk ↦ by simpa [hn, hnk, hb] using h_odd.bodd
--     have hT : M.IsTriangle {F[k + 2], F[k + 2 + 1], F[k + 2 + 2]} := by
--       simpa [hb] using hF.isTriangle_getElem (k + 2) (by grind)
--     obtain ⟨C', hC'ss, hC', h0C'⟩ := hC.strong_elimination hT.isCircuit hkC (by simp) h0C
--       (by simp [hF.nodup.getElem_inj_iff])
--     refine ⟨C', hC', h0C', fun i hilt hiC' ↦ ?_⟩
--     obtain ⟨(rfl | rfl | hiC), hik⟩ : (i = k + 2 ∨ i = k + 3 ∨ F[i + 1] ∈ C) ∧ ¬i = k + 1 := by
--       simpa [hF.nodup.getElem_inj_iff] using hC'ss hiC'
--     all_goals grind

/-- If `M` is a simple, cosimple matroid whose ground set is a fan, then the fan is even
and wraps around its own beginning.  -/
lemma IsFan.isTriangle_of_simple (F : M.Fan false c) {n : ℕ} (h3 : F.length = n + 2)
    (hM : M.Simple) (hM' : M✶.Simple) (hFE : {e | e ∈ F} = M.E) :
      Even F.length ∧ M.IsTriangle {F[n], F[n + 1]'(by grind), F[0]} := by
  obtain rfl | rfl | n := n
  · grind [hF.length_ge_four_of_eq_ground hFE]
  · grind [hF.length_ge_four_of_eq_ground hFE]
  have hnp : ¬M✶.Parallel F[0] F[1] := by
    rw [hM'.parallel_iff_eq (hF.dual.subset_ground (getElem_mem ..))]
    simp [hF.nodup.getElem_inj_iff]
  set m := if Odd n then n + 3 else n + 2 with hm
  have hmlt : m < F.length := by lia
  have hm_odd : Odd (m + 1) := by simp [hm, Nat.odd_add_one, apply_ite]
  -- Take away the last element if the fan is even, then find a circuit containing `F[0]`
  -- that intersects the fan in only possibly the last element.
  obtain ⟨C, hC, h0C, hlt⟩ :=
    (hF.take (show 2 ≤ m + 1 by grind) (by lia)).exists_isCircuit_first_mem_of_length_odd
    (by rwa [length_take_of_le (by lia)]) (by rwa [getElem_take, getElem_take])
  simp_rw [length_take_of_le (show m + 1 ≤ F.length by lia), getElem_take] at hlt
  have hss : C ⊆ {F[m], F[n + 3], F[0]} := by
    intro e he
    obtain ⟨rfl | i, hi, rfl⟩ := getElem_of_mem <| hC.subset_ground.trans hFE.symm.subset he
    · simp
    obtain hlt | hle := lt_or_ge i m
    all_goals grind
  obtain hn | hn := Nat.even_or_odd n
  · simp_rw [hm, if_neg (show ¬ Odd n by simpa)] at hss
    refine ⟨by grind, isTriangle_of_dep_of_encard_le
      (hC.dep.superset hss (by simp [insert_subset_iff, hF.get_mem_ground])) ?_⟩
    grw [encard_insert_le, encard_pair_le, show (2 : ℕ∞) + 1 = 3 from rfl]
  have hcard := encard_le_encard hss
  simp_rw [hm, if_pos hn] at hcard
  grw [insert_eq_of_mem (by simp), encard_pair_le, ← hC.girth_le_card, ← M.three_le_girth] at hcard
  norm_num at hcard

lemma IsFan.isTriangle_bDual_of_simple (F : M.Fan b c) {n : ℕ} (h3 : F.length = n + 2)
    (hM : M.Simple) (hM' : M✶.Simple) (hFE : {e | e ∈ F} = M.E) : Even F.length ∧
      (M.bDual b).IsTriangle {F[n], F[n + 1]'(by grind), F[0]} := by
  simpa using IsFan.isTriangle_of_simple (M := M.bDual (b)) (F := F) (c := c != b) (by simpa) h3
    (by cases b with simpa) (by cases b with simpa) (by simpa)
