module

public import WIP.Fan.Basic
public import Matroid.Connectivity.Triangle
public import Matroid.Connectivity.Separation.Vertical
public import Matroid.ForMathlib.List.Set

open Set List

variable {α : Type*} {M : Matroid α} {X Y C K T : Set α} {e f g x y : α} {b c d : Bool}
    {J : Bool → List α} {L : List α} {n i j p q r : ℕ} {F J : List α} {b c : Bool}

namespace Matroid.Fan



#exit

lemma IsFan.mem_iff_mem₁₂ (hF : M.IsFan F b c) (i C) (hi : i + 2 < F.length)
    (hC : (M.bDual (i.bodd == b)).IsCircuit C) (heC : F[i] ∉ C) : F[i + 1] ∈ C ↔ F[i + 2] ∈ C := by
  rw [(hF.isTriangle_getElem _ hi).mem_iff_mem_of_isCircuit_bDual _ heC]
  obtain rfl | rfl := b.eq_or_eq_not i.bodd
  <;> simpa using hC

lemma IsFan.mem_iff_mem₀₂ (hF : M.IsFan F b c) (i C) (hi : i + 2 < F.length)
    (hC : (M.bDual (i.bodd == b)).IsCircuit C) (heC : F[i + 1] ∉ C) : F[i] ∈ C ↔ F[i + 2] ∈ C := by
  refine (hF.isTriangle_getElem i hi).swap_left.mem_iff_mem_of_isCircuit_bDual ?_ heC
  obtain rfl | rfl := b.eq_or_eq_not i.bodd
  <;> simpa using hC

lemma IsFan.mem_iff_mem₀₁ (hF : M.IsFan F b c) (i C) (hi : i + 2 < F.length)
    (hC : (M.bDual (i.bodd == b)).IsCircuit C) (heC : F[i + 2] ∉ C) : F[i] ∈ C ↔ F[i + 1] ∈ C := by
  rw [(hF.isTriangle_getElem i hi).reverse.mem_iff_mem_of_isCircuit_bDual ?_ heC]
  obtain rfl | rfl := b.eq_or_eq_not i.bodd
  <;> simpa using hC

lemma IsFan.mem_or_mem₀₁ (hF : M.IsFan F b c) (i C) (hi : i + 2 < F.length)
    (hC : (M.bDual (i.bodd == b)).IsCircuit C) (heC : F[i + 2] ∈ C) : F[i] ∈ C ∨ F[i + 1] ∈ C := by
  refine (hF.isTriangle_getElem i hi).reverse.swap_right.mem_or_mem_of_isCircuit_bDual ?_ heC
  obtain rfl | rfl := b.eq_or_eq_not i.bodd
  <;> simpa using hC

lemma IsFan.mem_or_mem₀₂ (hF : M.IsFan F b c) (i C) (hi : i + 2 < F.length)
    (hC : (M.bDual (i.bodd == b)).IsCircuit C) (heC : F[i + 1] ∈ C) : F[i] ∈ C ∨ F[i + 2] ∈ C := by
  refine (hF.isTriangle_getElem i hi).swap_left.mem_or_mem_of_isCircuit_bDual ?_ heC
  obtain rfl | rfl := b.eq_or_eq_not i.bodd
  <;> simpa using hC

lemma IsFan.mem_or_mem₁₂ (hF : M.IsFan F b c) (i C) (hi : i + 2 < F.length)
    (hC : (M.bDual (i.bodd == b)).IsCircuit C) (heC : F[i] ∈ C) : F[i + 1] ∈ C ∨ F[i + 2] ∈ C := by
  refine (hF.isTriangle_getElem i hi).mem_or_mem_of_isCircuit_bDual ?_ heC
  obtain rfl | rfl := b.eq_or_eq_not i.bodd
  <;> simpa using hC

lemma IsFan.getElems_Ico_subset_closure (hF : M.IsFan F b c) (hp : p.bodd = b) (hq : q.bodd = !b)
    (hqF : q ≤ F.length) :
    F.getElems (Ico p q) ⊆ M.closure (F.getElems {i ∈ Ico p q | i.bodd = b}) := by
  obtain hpq | hpq := lt_or_ge q p
  · simp [Ico_eq_empty_of_le hpq.le]
  rw [getElems_subset_iff]
  rintro i hiF ⟨hpi, hiq⟩
  obtain rfl | rfl := b.eq_or_eq_not i.bodd
  · refine mem_closure_of_mem' _ (mem_getElems ?_ hiF) hF.get_mem_ground
    simp [hpi, hiq]
  obtain rfl | i := i
  · grind
  obtain rfl | hlt := hpi.eq_or_lt
  · simp at hp
  have hiq : i + 2 ≠ q := by
    rintro rfl
    simp at hq
  refine mem_of_mem_of_subset (hF.isTriangle_getElem_of_eq i (by lia) (by simp)).mem_closure₂ <|
    M.closure_subset_closure ?_
  grind [Nat.bodd_succ,  insert_subset_iff, hF.nodup.getElem_mem_getElems_iff]

/-- The joints are always independent, unless the first and last element are parallel joints. -/
lemma IsFan.joints_indep (hF : M.IsFan F b c)
    (h_pair : b = false → c = false → ¬ M.Parallel F[0] F[F.length - 1]) :
    M.Indep (F.getElems {i | i.bodd = b}) := by
  simp only [hF.nodup.subset_getElems_iff, mem_ofPred_eq, and_imp,
    indep_iff_forall_subset_not_isCircuit ((F.getElems_subset_toSet ..).trans hF.subset_ground)]
  intro C hCF hCodd hC
  by_cases hss : C ⊆ {F[0], F[F.length - 1]}
  · by_cases! h0 : F[0] ∉ C
    · exact hC.not_indep <| (hF.isNonloop (e := F[F.length - 1]) (by simp)).indep.subset <| by grind
    by_cases! hlen : F[F.length - 1] ∉ C
    · exact hC.not_indep <| (hF.isNonloop (e := F[0]) (by simp)).indep.subset <| by grind
    obtain rfl := hss.antisymm (by grind)
    obtain rfl : b = false := by simpa using hCodd 0 (by grind) (by simp)
    obtain rfl : c = false := by
      simpa [Nat.bodd_sub (show 1 ≤ F.length by grind), hF.length_bodd_eq] using
      hCodd (F.length - 1) (by grind) (by simp)
    refine h_pair rfl rfl <| ?_
    rw [(hF.isNonloop (by simp)).parallel_iff_dep (hF.isNonloop (by simp))]
    · exact hC.dep
    grind
  obtain ⟨x, hxC, hne⟩ := not_subset.1 hss
  obtain ⟨rfl | i, hi, rfl⟩ := getElem_of_mem (hCF hxC)
  · simp at hne
  obtain hne' : i + 1 ≠ F.length - 1 := by simpa [hF.nodup.getElem_inj_iff] using hne
  obtain rfl : (!i.bodd) = b := by simpa using hCodd _ hi hxC
  obtain hiC | hi2C := hF.mem_or_mem₀₂ i C (by lia) (by simpa) hxC
  · grind [hCodd i (by lia) hiC]
  simpa using hCodd (i + 2) _ hi2C

/-- Under an appropriate nondegeneracy assumption, any interval of joints or cojoints
is independent. -/
lemma IsFan.joints_Ico_indep (hF : M.IsFan F b c)
    (hpq : p = 0 → F.length ≤ q → b = false → c = false → ¬ M.Parallel F[0] F[F.length - 1]) :
    M.Indep (F.getElems {x ∈ Ico p q | x.bodd = b}) := by
  by_cases! hdg : b = false → c = false → ¬ M.Parallel F[0] F[F.length - 1]
  · exact (hF.joints_indep hdg).subset <| getElems_mono _ <| by grind
  obtain ⟨rfl, rfl, hpara⟩ := hdg
  simp only [hpara, not_true_eq_false, imp_false, not_le] at hpq
  wlog hq : q ≤ F.length generalizing q with aux
  · specialize aux (q := F.length) (by grind) rfl.le
    rwa [hF.nodup.getElems_ofPred_and, getElems_Ico, ← extract_min_right, min_eq_right (by lia)]
      at aux ⊢
  wlog hp : p ≠ 0 generalizing p q F with aux
  · obtain rfl : p = 0 := by lia
    refine (aux hF.reverse (q := F.length) (p := F.length - q) (by grind [parallel_comm])
      (by lia) (by simp) (by lia)).subset ?_
    rw [hF.nodup.getElems_ofPred_and, (nodup_reverse.2 hF.nodup).getElems_ofPred_and,
      getElems_Ico, getElems_Ico, extract_reverse, Nat.sub_self, Nat.sub_sub_self hq,
      getElems_reverse_bodd, hF.length_bodd_eq]
    simp
  refine ((hF.tail (by grind)).joints_indep (by simp)).subset ?_
  rw [getElems_tail]
  refine getElems_mono _ ?_
  rintro (rfl | i) <;> simp [hp]

lemma IsFan.eRk_eq (hF : M.IsFan F b b) (hpara : ¬ (M.bDual b).Parallel F[0] (F[F.length - 1])) :
    2 * (M.bDual b).eRk {e | e ∈ F} = F.length + 1 := by
  obtain h2 | h3 := hF.two_le_length.eq_or_lt
  · have hcon := h2 ▸ hF.bool_right_eq
    simp at hcon
  refine le_antisymm (by simpa using (hF.bDual b).eRk_le (by lia)) ?_
  have hrw := hF.nodup.getElems_bodd_encard (b != b)
  simp only [bne_self_eq_false, hF.length_bodd_eq, BEq.rfl, Bool.and_true, Bool.toNat_false,
    Nat.cast_zero, add_zero, Bool.not_false, Bool.and_self, Bool.toNat_true, Nat.cast_one] at hrw
  grw [← ((hF.bDual b).joints_indep (by simp [hpara])).encard_le_eRk_of_subset
    (getElems_subset_toSet ..), ← hrw, bne_self_eq_false]

/-- In a fan of length at least five, we can contract the head and remain a fan, unless
the head is a cojoint in parallel with the second element, or a joint in parallel with the last. -/
lemma IsFan.contract_head' (hF : M.IsFan F b c) (h5 : 5 ≤ F.length)
    (h_init : b = true → ¬ M.Parallel F[0] F[1])
    (h_pair : b = false → c = false → ¬ M.Parallel F[0] F[F.length - 1]) :
    (M ／ {F[0]}).IsFan F.tail (!b) c := by
  rw [isFan_iff_forall (by grind)]
  simp_rw [length_tail, hF.length_sub_one_bodd_eq, ← Bool.bnot_bne]
  simp only [Bool.not_bne, Bool.bnot_bne, Bool.not_eq_eq_eq_not, getElem_tail, true_and,
    hF.nodup.sublist (tail_sublist F)]
  intro i hi
  obtain rfl | rfl := b.eq_or_eq_not i.bodd
  · simp [add_assoc, hF.isTriad_getElem_of_eq (i + 1) (by lia) (by simp), hF.nodup.getElem_inj_iff]
  simp only [Bool.not_beq_self, bDual_false, add_assoc, Nat.reduceAdd, isTriangle_iff]
  have hT := hF.isTriangle_getElem_of_eq (i + 1) (by lia) (by simp)
  refine ⟨Skew.isCircuit_contract ?_ hT.isCircuit (by simp [hF.nodup.getElem_inj_iff]),
    hT.three_elements⟩
  rw [(hF.isNonloop (by simp)).skew_left_iff, insert_comm, closure_insert_eq_of_mem_closure
    hT.mem_closure₂]
  intro hcl
  obtain ⟨C, hCss, hC, h0C⟩ := exists_isCircuit_of_mem_closure hcl
    (by simp [hF.nodup.getElem_inj_iff])
  obtain rfl | i := i
  · by_cases h3 : F[3] ∈ C
    · obtain h' | h' := hF.mem_or_mem₀₂ 2 C (by lia) (by simpa) h3 <;>
      simpa [hF.nodup.getElem_inj_iff] using hCss h'
    rw [pair_comm, insert_comm, subset_insert_iff_of_notMem h3] at hCss
    exact h_init rfl <| ((hF.isNonloop (by simp)).parallel_iff_dep (hF.isNonloop (by simp))
      (by simp [hF.nodup.getElem_inj_iff])).2 <| hC.dep.superset hCss
  by_cases hi1 : F[i + 2] ∈ C
  · obtain h' | h' := hF.mem_or_mem₀₂ (i + 1) C (by lia) (by simpa) hi1 <;>
    simpa [hF.nodup.getElem_inj_iff] using hCss h'
  cases hi : i.bodd
  · grw [insert_comm, subset_insert_iff_of_notMem hi1] at hCss
    have hpara := ((hF.isNonloop (by simp)).parallel_iff_dep (hF.isNonloop (by simp))
      (by simp [hF.nodup.getElem_inj_iff])).2 <| hC.dep.superset hCss
    by_cases heq : i + 5 = F.length
    · exact h_pair (by simpa) (by simp [hF.bool_right_eq, ← heq]) <| by grind
    have hwin := (hF.isTriangle_getElem (i + 3) (by lia)).isCircuit.mem_iff_mem_of_parallel_bDual
      (e := F[0]) (f := F[i + 4]) (by simpa)
    simp [hF.nodup.getElem_inj_iff] at hwin
  obtain h' | h' := hF.mem_or_mem₁₂ 0 C (by lia) (by simpa [hi]) h0C <;>
  simpa [hF.nodup.getElem_inj_iff, show i ≠ 0 by grind] using hCss h'

lemma IsFan.delete_head' (hF : M.IsFan F b c) (h5 : 5 ≤ F.length)
    (h_init : b = false → ¬ M✶.Parallel F[0] F[1])
    (h_pair : b = true → c = true → ¬ M✶.Parallel F[0] F[F.length - 1]) :
    (M ＼ {F[0]}).IsFan F.tail (!b) c := by
  simpa using (hF.dual.contract_head' h5 (by simpa) (by simpa)).dual

lemma IsFan.remove_head (hF : M.IsFan F b c) (h5 : 5 ≤ F.length) {d : Bool}
    (h_init : b = d → ¬ (M.bDual !d).Parallel F[0] F[1])
    (h_pair : b = !d → c = !d → ¬ (M.bDual !d).Parallel F[0] F[F.length - 1]) :
    (M.remove d {F[0]}).IsFan F.tail (!b) c := by
  obtain rfl | rfl := d
  · exact hF.delete_head' h5 (by simpa) (by simpa)
  exact hF.contract_head' h5 (by simpa) (by simpa)

-- lemma IsFan.delete_head' (hF : M.IsFan F b c) (h3 : 3 ≤ F.length)
--     (h_tri : (F.length = 3 ∨ b = false) → ¬ M✶.Parallel F[0] F[1])
--     (h4 : F.length ≤ 4 → ¬ M✶.Parallel F[0] F[2])
--     (h_pair : b = false → c = false → ¬ M✶.Parallel F[0] F[F.length - 1]) :
--     (M ＼ {F[0]}).IsFan F.tail (!b) c := by
--   induction hF with
--   | of_pair => simp at h3
--   | cons_triangle e x y F b c h heF hT ih =>
--   suffices (M ＼ {e}).IsFan (x :: y :: F) b c by simpa
--   cases F with
--   | nil =>
--     suffices (M ＼ {e}).IsFan [x, y] b (!b) by simpa [h.bool_right_eq]
--     refine isFan_pair ?_ ?_ (by grind)
--     · rintro (rfl | rfl)
--       · exact delete_isNonloop_iff.2 ⟨(h.isNonloop (by simp)), hT.ne₁₂.symm⟩
--       suffices x ∉ M✶.closure {e} by simpa [show x ∈ M.E from h.subset_ground (by simp)]
--       rw [← bDual_true, ← (h.isNonloop_bDual (by simp) _).parallel_iff_mem_closure, parallel_com
--       simpa using h_tri
--     rintro (rfl | rfl)
--     · exact delete_isNonloop_iff.2 ⟨(h.isNonloop (by simp)), hT.ne₁₃.symm⟩
--     suffices y ∉ M✶.closure {e} by simpa [show y ∈ M.E from h.subset_ground (by simp)]
--     rw [← bDual_true, ← (h.isNonloop_bDual (by simp) _).parallel_iff_mem_closure, parallel_comm]
--     simpa using h4
--   | cons z F =>
--     simp only [mem_cons, not_or, length_cons, le_add_iff_nonneg_left, zero_le, Nat.reduceEqDiff,
--       length_eq_zero_iff, getElem_cons_zero, getElem_cons_succ, Order.add_one_le_iff,
--       add_tsub_cancel_right, tail_cons, forall_true_left, Bool.not_eq_eq_eq_not, Bool.not_false,
--       false_or] at *
--     specialize ih ?_ ?_ ?_
--     · rintro (rfl | rfl) hpara
--       ·
--     _


--   _

/-- Probably this should be proved by reverse induction instead. TODO -/
lemma IsFan.contract_head (hF : M.IsFan F false c) (h3 : 3 ≤ F.length)
    (h_pair : c = false → ¬ M.Parallel F[0] F[F.length - 1]) :
    (M ／ {F[0]}).IsFan F.tail true c := by
  obtain h3 | hlt := h3.eq_or_lt
  · rw [eq_comm, length_eq_three] at h3
    obtain ⟨e, f, g, rfl⟩ := h3
    obtain rfl : c = false := by simpa using hF.bool_right_eq
    suffices (M ／ {e}).IsFan [f, g] true false by simpa
    have hT : M.IsTriangle {e, f, g} := hF.isTriangle_getElem_of_eq 0 (by lia) rfl
    refine IsFan.of_pair _ _ _ _ ?_ ?_ (by grind [hF.nodup])
    · rw [Bool.forall_bool, bDual_false, bDual_true, dual_contract, delete_isNonloop_iff]
      exact ⟨hT.parallel_contract₁.isNonloop_left, hT.isNonloop_bDual₂ (b := true), hT.ne₁₂.symm⟩
    rw [Bool.forall_bool, bDual_false, bDual_true, dual_contract, delete_isNonloop_iff]
    exact ⟨hT.parallel_contract₁.isNonloop_right, hT.isNonloop_bDual₃ (b := true), hT.ne₁₃.symm⟩
  rw [isFan_iff_forall (by grind), and_iff_right (show F.tail.Nodup from hF.nodup.tail)]
  match F with
  | [] => grind [hF.two_le_length]
  | e :: F =>
    obtain rfl := hF.bool_right_eq
    simp only [length_cons, Nat.bodd_succ, Bool.false_beq, Bool.not_not, Bool.true_beq, tail_cons,
      getElem_cons_zero, Bool.true_bne, true_and]
    intro i hi
    have hT := hF.isTriangle_getElem (i + 1) (by grind)
    simp only [Nat.bodd_succ, Bool.bne_not, Bool.false_bne, getElem_cons_succ] at hT
    cases h : i.bodd
    · simp only [Bool.not_false, bDual_true, dual_contract, isTriangle_delete_iff,
        dual_isTriangle_iff, disjoint_singleton_right]
      suffices M.IsTriad {F[i], F[i + 1], F[i + 2]} by grind [hF.nodup]
      simpa [h] using hT
    rw [Bool.not_true, bDual_false, isTriangle_iff, and_iff_left hT.three_elements]
    have hF' := hF.tail (by grind)
    simp only [tail_cons, Bool.not_false, length_cons, Nat.bodd_succ, Bool.false_beq,
      Bool.not_not] at hF'
    refine Skew.isCircuit_contract_of_nontrivial ?_ (by simpa [h] using hT.isCircuit) hT.nontrivial
    have hsk := (hF.joints_indep (by simpa using h_pair)).subset_skew_diff (J := {e})
      (by grind [getElems])
    refine hsk.closure_skew_right.mono_right ?_
    grw [getElems_cons_of_mem _ _ (by simp), insert_sdiff_self_of_notMem (by grind [hF.nodup]),
      ← getElems_Ico_eq_triple, hF'.getElems_Ico_subset_closure h (by simpa) (by lia)]
    exact M.closure_subset_closure <| getElems_mono _ <| by simp

/-- Let `F[p]` and `F[q]` be joints of a fan, and `K` be the set of cojoints between `p` and `q`.
If `F[p]` and `F[q]` are not parallel and at the beginning and the end of the fan,
then `{F[p], F[q]} ∪ K` is a circuit.

The nondegeracy hypothesis has some redundancy, since `i = 0` and `q + 1 = F.length` implies that
`b = c = false`; we include it so it is easier to discharge quickly in various cases.  -/
lemma IsFan.isCircuit_interval (hF : M.IsFan F b c) (hpq : p < q) (hqF : q < F.length)
    (hpb : p.bodd = b) (hqb : q.bodd = b)
    (hdg : b = false → c = false → p = 0 → q + 1 = F.length → ¬ M.Parallel F[0] F[F.length - 1]) :
    M.IsCircuit <| F.getElems (insert p (insert q {i ∈ Ico p q | i.bodd = !b})) := by
  induction q using Nat.strong_induction_on with | h q ih =>
  obtain ⟨q, hqlt, rfl, rfl | hlt⟩ : ∃ q' < q, q' + 2 = q ∧ (q' = p ∨ p < q') := by
    obtain ⟨rfl | rfl | d, rfl⟩ := exists_add_of_le hpq.le
    · lia
    · simp [hpb] at hqb
    exact ⟨p + d, by grind⟩
  · rw [getElems_insert _ _ (by lia), getElems_insert _ _ (by lia), hF.nodup.getElems_ofPred_and,
      getElems_Ico_eq_pair _ _ (by lia), insert_inter_of_notMem (by simpa [hF.nodup]),
      singleton_inter_of_mem (by simpa [hF.nodup]), pair_comm]
    exact (hF.isTriangle_getElem_of_eq q (by lia) hpb).isCircuit
  simp only [Nat.bodd_succ, Bool.not_not] at hqb
  specialize ih q hqlt hlt (by lia) hqb (by grind)
  rw [getElems_insert _ _ (by lia), getElems_insert _ _ (by lia)] at ih ⊢
  have hT := (hF.isTriangle_getElem_of_eq q (by lia) hqb).swap_right
  convert hT.union_diff_singleton_isCircuit ih (by simp [hF.nodup]) ?_ using 1
  · simp_rw [insert_comm F[p], ← one_add_one_eq_two, ← add_assoc,
      hF.nodup.getElems_ofPred_and, getElems_Ico]
    rw [extract_add_one_right _ (by lia) (by lia), extract_add_one_right _ (by lia) (by lia),
      insert_sdiff_self_of_notMem (by simp [hF.nodup, hF.nodup.getElem_inj_iff, hlt.ne.symm])]
    simp only [append_assoc, cons_append, nil_append, mem_append, mem_cons, ofPred_or,
      not_mem_nil, or_false, ofPred_eq_eq_singleton, union_singleton, union_insert]
    rw [insert_inter_of_mem (by simpa [hF.nodup]), insert_inter_of_notMem (by simpa [hF.nodup])]
    grind
  grw [hF.nodup.getElems_ofPred_and, inter_subset_left,
    insert_eq_of_mem (by simp [hF.nodup, hlt]), getElems_Ico, ← toSet_concat_eq,
    ← extract_add_one_right _ hlt.le, ← getElems_Ico,
    hF.getElems_Ico_subset_closure hpb (by simpa) (by lia), M.closure_closure,
    (hF.joints_Ico_indep <| by grind).notMem_closure_iff_of_notMem (by simp [hF.nodup])]
  exact (hF.joints_Ico_indep (p := p) (q := q + 3) (by grind)).subset
    <| insert_subset (by simpa [hF.nodup, hpq.le]) <| getElems_mono _ <| by grind

/-- If a circuit of a matroid contains joints `F[p + 1], F[q]` of a fan `F`,
and does not contain the cojoint `F[p]`,
then it comprises precisely `F[p + 1], F[q]`, and the cojoints between them.  -/
lemma IsFan.eq_interval_of_notMem_mem_mem (hF : M.IsFan F b c) (hpq : p + 1 < q)
    (hqF : q < F.length) (hpb : p.bodd = !b) (hqb : q.bodd = b) (hC : M.IsCircuit C)
    (hpC : F[p] ∉ C) (hp1C : F[p + 1] ∈ C) (hqC : F[q] ∈ C) :
    C = (F.getElems (insert (p + 1) <| insert q <| {i ∈ Ico (p + 1) q | i.bodd = !b})) := by
  induction q using Nat.strong_induction_on with | h q ihq =>
  suffices aux : (F.getElems (insert (p + 1) <| insert q <| {i ∈ Ico (p + 1) q | i.bodd = !b})) ⊆ C
  · exact hC.eq_of_superset_isCircuit (hF.isCircuit_interval (by lia) hqF (by simpa) hqb (by simp))
      aux
  suffices ∀ i (hi : i + 1 < F.length), p < i → i < q → i.bodd = !b → F[i] ∈ C from
    getElems_subset_iff.2 <| fun i hi ↦ by grind
  intro i hi hpi hiq hib
  have hp2 : F[p + 2] ∈ C := by rwa [← hF.mem_iff_mem₁₂ (C := C) p (by lia) (by simpa [hpb]) hpC]
  induction i using Nat.twoStepInduction with
  | zero => grind
  | one => grind
  | more i ih =>
    obtain rfl | rfl := b.eq_or_eq_not i.bodd
    · simp at hib
    obtain rfl | hne := eq_or_ne p i
    · assumption
    obtain rfl | hne := eq_or_ne p (i + 1)
    · simp at hpb
    by_cases h1 : F[i + 1] ∈ C
    · rw [ihq (i + 1) (by lia) (by grind) (by lia) (by simp) hpC hp1C h1] at hqC
      simp [hF.nodup, hqb, show q ≠ i + 1 by lia, hpq.ne.symm] at hqC
    rw [← hF.mem_iff_mem₀₂ _ _ (by lia) (by simpa) h1]
    exact ih (by lia) (by lia) (by lia) (by simp)

lemma IsFan.exists_eq_interval_of_notMem_mem_add_one (hF : M.IsFan F b c) (hpq : p + 1 < q)
    (hqF : q < F.length) (hpb : p.bodd = !b) (hqb : q.bodd = !b) (hC : M.IsCircuit C)
    (hpC : F[p] ∉ C) (hp1C : F[p + 1] ∈ C) (hqC : F[q] ∉ C) :
    ∃ (r : ℕ) (_ : p + 1 < r) (_ : r < q), r.bodd = b ∧
    C = F.getElems (insert (p + 1) <| insert r <| {i ∈ Ico (p + 1) r | i.bodd = !b}) := by
  by_cases! hr : ¬ (∀ r (hr : r < q), p + 1 < r → r.bodd = !p.bodd → F[r] ∉ C)
  · push Not at hr
    obtain ⟨r, hrq, hpr, hrb, hrC⟩ := hr
    exact ⟨r, hpr, by lia, (by simpa [hrb] using hpb),
      hF.eq_interval_of_notMem_mem_mem hpr (by lia) hpb (by simpa [hrb] using hpb) hC hpC hp1C hrC⟩
  refine False.elim <| hqC ?_
  clear hqC
  obtain ⟨d, rfl⟩ := exists_add_of_le (show p + 2 ≤ q by lia)
  induction d using Nat.twoStepInduction with
  | zero => grind [hF.mem_or_mem₀₂ p C (by lia) (by simpa [hpb]) hp1C]
  | one => simp [hpb] at hqb
  | more d ih =>
    simp_rw [← add_assoc]
    simp only [Nat.bodd_add, Nat.bodd_succ, Bool.not_not] at hqb
    rw [← hF.mem_iff_mem₀₂ _ _ (by simpa) (by simpa [hqb])]
    · exact ih (by lia) (by lia) (by simpa) hpC hp1C (by grind)
    apply hr _ (by lia) (by lia)
    rw [Nat.bodd_succ, Bool.not_inj_iff, hpb]
    simpa

/-- If a circuit doesn't contain two particular cojoints `F[s], F[t]` of a fan `F`,
but it contains something between them, then it is an interval. -/
lemma IsFan.exists_eq_interval_of_notMem_mem_notMem {s t r : ℕ} (hF : M.IsFan F b c) (hsr : s < r)
    (hrt : r < t) (ht : t < F.length) (hsb : s.bodd = !b) (htb : t.bodd = !b)
    (hC : M.IsCircuit C) (hsC : F[s] ∉ C) (hrC : F[r] ∈ C) (htC : F[t] ∉ C) :
    ∃ (p q : ℕ) (_ : s < p) (_ : p < q) (_ : q < t), p.bodd = b ∧ q.bodd = b ∧
    C = F.getElems (insert p <| insert q <| {i ∈ Ico p q | i.bodd = !b}) := by
  induction h : r - s using Nat.strong_induction_on generalizing r s with | h d ih =>
  by_cases hs1 : F[s + 1] ∈ C
  · obtain ⟨j, hsj, hjt, rfl, rfl⟩ :=
      hF.exists_eq_interval_of_notMem_mem_add_one (by lia) ht hsb htb hC hsC hs1 htC
    exact ⟨s + 1, j, by simp [hsb, hsj, hjt]⟩
  have hs1i : s + 1 < r := by grind
  rw [hF.mem_iff_mem₁₂ _ _ (by lia) (by simpa [hsb]) hsC] at hs1
  obtain ⟨p, q, hpq⟩ := ih (r - (s + 2)) (by lia) (by grind) hrt (by simpa) hs1 hrC rfl
  exact ⟨p, q, by grind⟩

/-- A parallel pair in a fan is hard to find; it must either comprise both ends, or two consecutive
elements at one of the ends. The upper bound of 6 is best-possible,
since the `5`-fan `[0, 1, 2, 3, 4]` can have the pairs `[0, 2]` and `[1, 3]` both parallel. -/
lemma IsFan.eq_eq_of_parallel (h : M.IsFan F b c) (hF : 6 ≤ F.length) {hi : i < F.length}
    {hj : j < F.length} (hij : i < j) (hC : M.Parallel F[i] F[j]) :
    (b = true ∧ i = 0 ∧ j = 1) ∨ (c = true ∧ i + 2 = F.length ∧ j + 1 = F.length) ∨
    b = false ∧ c = false ∧ i = 0 ∧ j + 1 = F.length := by
  replace hC := hC.isCircuit_of_ne (by grind)
  obtain ⟨rfl | rfl | d, rfl⟩ := Nat.exists_eq_add_of_lt hij
  · obtain rfl | i := i
    · obtain rfl | rfl := b
      · exact False.elim <| (h.isTriangle_bDual (by lia)).indep₁₂.not_dep hC.dep
      simp
    obtain hib | hib := i.bodd.eq_or_eq_not b
    · exact False.elim <| (h.isTriangle_getElem_of_eq i (by lia) hib).indep₂₃.not_dep hC.dep
    by_cases hle : i + 3 < F.length
    · exact False.elim <| (h.isTriangle_getElem_of_eq (i + 1) (by lia) (by simpa)).indep₁₂.not_dep
        hC.dep
    simp [h.bool_right_eq, (show F.length = i + 3 by lia), hib]
  · obtain hib | hib := i.bodd.eq_or_eq_not b
    · exact False.elim <| (h.isTriangle_getElem_of_eq i (by lia) hib).indep₁₃.not_dep hC.dep
    by_cases! h2i : i < 2
    · have hcon := h.mem_or_mem₁₂ (i + 2) (C := {F[i], F[i + 2]}) (by lia) (by simpa [hib] using hC)
      simp [h.nodup.getElem_inj_iff, add_assoc] at hcon
    obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' h2i
    have hwin := h.mem_or_mem₀₁ i {F[i + 2], F[i + 4]} (by lia) <| by
      simpa [show i.bodd = !b by simpa using hib]
    simp [h.nodup.getElem_inj_iff] at hwin
  obtain rfl | i := i
  · obtain rfl | rfl := b
    · cases hdb : d.bodd
      · have hcon := h.mem_or_mem₀₁ (d + 1) {F[0], F[d + 3]} (by lia) (by simpa [hdb] using hC)
        simp [h.nodup.getElem_inj_iff] at hcon
      obtain h_eq | hne := eq_or_ne (d + 4) F.length
      · simpa [← h_eq, h.bool_right_eq]
      have hcon := h.mem_or_mem₀₂ (d + 2) {F[0], F[d + 3]} (by lia) (by simpa [hdb] using hC)
      simp [h.nodup.getElem_inj_iff] at hcon
    have hcon := h.mem_or_mem₁₂ 0 {F[0], F[d + 3]} (by lia) (by simpa using hC)
    simp [h.nodup.getElem_inj_iff] at hcon
  exfalso
  simp only [add_assoc, add_comm 1, Nat.reduceAdd] at hC
  obtain hib | hib := i.bodd.eq_or_eq_not b
  · have hcon := h.mem_or_mem₁₂ (i + 1) {F[i + 1], F[i + (d + 4)]} (by lia) (by simpa [hib])
    grind [h.nodup.getElem_inj_iff]
  have hcon := h.mem_or_mem₀₂ i {F[i + 1], F[i + (d + 4)]} (by lia) (by simpa [hib])
  simp [h.nodup.getElem_inj_iff] at hcon

-- lemma IsFan.delete_head'' (hF : M.IsFan F b c) (h3 : 3 ≤ F.length)
--     -- (h3 : F.length = 2 → ¬ )
--     (h_tri : b = true → ¬ M✶.Parallel F[0] F[1])
--     (h4 : b = false → F.length = 4 → ¬ M✶.Parallel F[0] F[2])
--     (h_pair : b = false → c = false → ¬ M✶.Parallel F[0] F[F.length - 1]) :
--     (M ＼ {F[0]}).IsFan F.tail (!b) c := by
--   match F with
--   | [] => simp at h3
--   | [_] => simp at h3
--   | [_, _] => simp at h3
--   | e :: f :: g :: F =>
--   simp only [getElem_cons_zero, getElem_cons_succ, length_cons, add_tsub_cancel_right,
--     tail_cons] at *
--   induction F using List.reverseRecOn generalizing c with
--   | nil =>
--     sorry
--   | append_singleton F a ih =>

--     specialize ih (by simpa [dropLast_cons_of_ne_nil] using hF.dropLast (by simp)) (by simp)
-- ?_ ?_
--     · rintro rfl hFl hpara
--       obtain ⟨y, rfl⟩ := (length_eq_one_iff (l := F)).1 (by lia)
--       have := (hF.isTriangle_getElem_of_eq 2 (by simp) rfl).isCircuit.mem_iff_mem_of_parallel_du
--         hpara
--       grind [hF.nodup]
--     · simp
--       rintro rfl rfl hpara
--       cases F with
--       | nil => exact h4 rfl rfl hpara
--       | cons y F =>
--         have hTP := (hF.isTriangle_bDual (by simp)).isCircuit.mem_iff_mem_of_parallel_bDual hpara
--         simp only [length_cons, getElem_cons_succ] at hTP
--         grind [hF.nodup]
--     have := ih.concat (e := a)
--     simp at this
--     _






  --

lemma IsFan.delete_head (hF : M.IsFan F true c) (h3 : 3 ≤ F.length)
    (h_pair : c = true → ¬ M✶.Parallel F[0] F[F.length - 1]) :
    (M ＼ {F[0]}).IsFan F.tail false c := by
  simpa using (hF.dual.contract_head h3 (by simpa)).dual

lemma IsFan.contract_head_three (hF : M.IsFan F b c) (h3 : F.length = 3)
    (hnp₁ : b = true → ¬ M.Parallel F[0] F[1]) (hnp₂ : b = true → ¬ M.Parallel F[0] F[2]) :
    (M ／ {F[0]}).IsFan F.tail (!b) c := by
  rw [length_eq_three] at h3
  obtain ⟨e, f, g, rfl⟩ := h3
  obtain rfl : b = c := by simpa using hF.bool_left_eq
  suffices (M ／ {e}).IsFan [f, g] (!b) (!!b) by simpa
  have hT : (M.bDual b).IsTriangle {e, f, g} := by simpa using hF.isTriangle_getElem 0 (by lia)
  refine IsFan.of_pair _ _ _ _ ?_ ?_ hT.ne₂₃
  · rintro (rfl | rfl)
    · obtain rfl | rfl := b
      · exact hT.parallel_contract₁.isNonloop_left
      simp only [bDual_false, contract_isNonloop_iff, mem_sdiff]
      rw [← hT.isNonloop_of_bDual₂.parallel_iff_mem_closure, parallel_comm,
        and_iff_right (IsTriad.mem_ground₂ hT)]
      exact hnp₁ rfl
    simpa [hT.ne₁₂.symm] using hT.isNonloop_bDual₂ (b := !b)
  rintro (rfl | rfl)
  · obtain rfl | rfl := b
    · exact hT.parallel_contract₁.isNonloop_right
    replace baz : ¬ M.Parallel e g := by simpa using hnp₂
    rw [parallel_comm, hT.isNonloop_of_bDual₃.parallel_iff_mem_closure] at baz
    simp [baz, IsTriad.mem_ground₃ hT]
  simpa [hT.ne₁₃.symm] using hT.isNonloop_bDual₃ (b := !b)

@[grind .]
lemma IsFan.length_ge_four_of_eq_ground [M.Simple] [M✶.Simple] (hF : M.IsFan F b c)
    (hFE : {e | e ∈ F} = M.E) : 4 ≤ F.length := by
  have hF2 := hF.two_le_length
  have hr := M.eRk_pair_eq (e := F[0]) (f := F[1]) (by simp [hF.nodup.getElem_inj_iff])
    (hF.get_mem_ground (i := 0)) (hF.get_mem_ground (i := 1))
  have hr1 := M✶.eRk_pair_eq (e := F[0]) (f := F[1]) (by simp [hF.nodup.getElem_inj_iff])
    (hF.get_mem_ground (i := 0)) (hF.get_mem_ground (i := 1))
  have hle := encard_le_encard hFE.symm.subset
  grw [← eRank_add_eRank_dual, F.encard_toSet_le, ← M.eRk_le_eRank {F[0], F[1]},
    ← M✶.eRk_le_eRank {F[0], F[1]}, hr, hr1] at hle
  enat_to_nat!; lia

/-- If `F` is a fan whose ends are joints, and `C` is a circuit containing the first but not
the second element of `F`, then `M` has a circuit containing the first element of `F`,
and no other elements of `F` except possibly the last.  -/
lemma IsFan.exists_isCircuit_subset_first_last (hF : M.IsFan F false false)
    (hC : M.IsCircuit C) (h0C : F[0] ∈ C) (h1C : F[1] ∉ C) :
    ∃ C₀ ⊆ insert F[F.length - 1] C, M.IsCircuit C₀ ∧ F[0] ∈ C₀ := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hF.two_le_length
  suffices aux : ∀ k ≤ n, ∃ C₀, M.IsCircuit C₀ ∧ F[0] ∈ C₀ ∧ C₀ ⊆ C ∪ {e | e ∈ F} ∧
      ∀ i (hi : i + 1 < F.length), F[i + 1] ∈ C₀ → k ≤ i by
    refine Exists.imp ?_ <| aux n rfl.le
    simp only [and_imp]
    refine fun C₀ hC₀ h0C₀ hC₀ss h ↦ ⟨?_, hC₀, h0C₀⟩
    refine fun e heC₀ ↦ ?_
    by_cases heC : e ∈ C
    · exact .inr heC
    obtain ⟨rfl | i, hi, rfl⟩ := getElem_of_mem (show e ∈ F by grind)
    · grind
    obtain rfl : n = i := by grind
    simp [hn, add_comm]
  rintro (rfl | k) hk
  · use C; grind
  induction k with
  | zero => use C; grind
  | succ k ih =>
    obtain ⟨C₀', hC₀', h0C₀', hC₀'ss, hClt⟩ := ih (by lia)
    obtain hkC | hkC := em' (F[k + 2] ∈ C₀')
    · exact ⟨C₀', by grind⟩
    cases hb : !k.bodd
    · have hT' := (hF.isTriad_getElem_of_eq k (by lia) (by simpa using hb)).reverse
      obtain h1 | h2 := hT'.mem_or_mem_of_isCocircuit (K := C₀') (by simpa) hkC
      · grind [hClt _ _ h1]
      obtain rfl | k := k
      · grind
      grind [hClt _ _ h2]
    obtain rfl | hlt := hk.eq_or_lt
    · simpa [hn, ← hb] using hF.length_bodd_eq
    have hT := hF.isTriangle_getElem_of_eq (k + 2) (by lia) (by simpa using hb)
    have elim := hC₀'.strong_elimination hT.isCircuit (e := F[k + 2]) (f := F[0]) hkC (by simp)
      h0C₀' (by simp [hF.nodup.getElem_inj_iff])
    obtain ⟨C₀, hC₀ss, hC₀, h0C₀⟩ := elim
    refine ⟨C₀, hC₀, h0C₀, ?_, fun i hi hiC₀ ↦ by grind [hF.nodup.getElem_inj_iff]⟩
    grw [hC₀ss, hC₀'ss, sdiff_subset]
    grind [Set.union_subset_iff, insert_subset_iff]

/-- For any fan `F = [a, b, ..., z]` whose ends are joints and for which `{a, b}` isn't series,
there is a circuit `C` with `a ∈ C ∩ F ⊆ {a, z}`. -/
lemma IsFan.exists_isCircuit_first_mem_of_length_odd (hF : M.IsFan F false c)
    (h_odd : Odd F.length) (h01 : ¬ M✶.Parallel (F[0]'(by grind)) (F[1]'hF.two_le_length)) :
    ∃ C, M.IsCircuit C ∧ F[0] ∈ C ∧ ∀ i (hi : i + 1 < F.length),
      F[i + 1] ∈ C → i + 2 = F.length := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le hF.two_le_length
  suffices aux : ∀ k ≤ n, ∃ C, M.IsCircuit C ∧ F[0] ∈ C ∧
      ∀ i (hi : i + 1 < F.length), F[i + 1] ∈ C → k ≤ i from
    Exists.imp (by grind) <| aux n rfl.le
  rw [parallel_dual_iff_forall_circuit (hF.dual.isNonloop (by simp)) hF.get_mem_ground] at h01
  simp_rw [not_forall, exists_prop] at h01
  intro k hk
  induction k with
  | zero => exact Exists.imp (by grind) h01
  | succ k ih =>
    obtain rfl | k := k
    · exact Exists.imp (by grind) h01
    obtain ⟨C, hC, h0C, hClt⟩ := ih (by lia)
    obtain hkC | hkC := em' (F[k + 2] ∈ C)
    · exact ⟨C, by grind⟩
    by_cases hb : k.bodd = true
    · obtain hwin | hwin := (hF.isTriangle_getElem k (by lia)).reverse.mem_or_mem_of_isCircuit_bDual
        (by simpa [hb]) hkC
      · grind
      obtain rfl | k := k; simp at hb
      grind
    have hnk : n ≠ k + 2 := fun hnk ↦ by simpa [hn, hnk, hb] using h_odd.bodd
    have hT : M.IsTriangle {F[k + 2], F[k + 2 + 1], F[k + 2 + 2]} := by
      simpa [hb] using hF.isTriangle_getElem (k + 2) (by grind)
    obtain ⟨C', hC'ss, hC', h0C'⟩ := hC.strong_elimination hT.isCircuit hkC (by simp) h0C
      (by simp [hF.nodup.getElem_inj_iff])
    refine ⟨C', hC', h0C', fun i hilt hiC' ↦ ?_⟩
    obtain ⟨(rfl | rfl | hiC), hik⟩ : (i = k + 2 ∨ i = k + 3 ∨ F[i + 1] ∈ C) ∧ ¬i = k + 1 := by
      simpa [hF.nodup.getElem_inj_iff] using hC'ss hiC'
    all_goals grind

/-- If `M` is a simple, cosimple matroid whose ground set is a fan, then the fan is even
and wraps around its own beginning.  -/
lemma IsFan.isTriangle_of_simple (hF : M.IsFan F false c) {n : ℕ} (h3 : F.length = n + 2)
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

lemma IsFan.isTriangle_bDual_of_simple (hF : M.IsFan F b c) {n : ℕ} (h3 : F.length = n + 2)
    (hM : M.Simple) (hM' : M✶.Simple) (hFE : {e | e ∈ F} = M.E) : Even F.length ∧
      (M.bDual b).IsTriangle {F[n], F[n + 1]'(by grind), F[0]} := by
  simpa using IsFan.isTriangle_of_simple (M := M.bDual (b)) (F := F) (c := c != b) (by simpa) h3
    (by cases b with simpa) (by cases b with simpa) (by simpa)

lemma IsFan.eConn_le_two (h : M.IsFan F b c) : M.eConn {e | e ∈ F} ≤ 2 := by
  obtain hFl | hFl := lt_or_ge F.length 3
  · grw [eConn_le_encard, encard_toSet_le]
    enat_to_nat! <;> lia
  grw [← ENat.add_le_add_iff_right (k := F.length) (by simp), ← h.nodup.encard_toSet_eq,
    ← eRk_add_eRk_dual_eq _ _ h.subset_ground,
    ← ENat.mul_le_mul_left_iff (a := 2) (by simp) (by simp), mul_add, h.eRk_le hFl,
    h.dual.eRk_le hFl, h.nodup.encard_toSet_eq]
  cases b with cases c with (simp; enat_to_nat!; lia)

/-- If the head is spanned by the tail in the appropriate dual of `b`, then the fan
has connectivity one. -/
lemma IsFan.eConn_le_one_of_mem_closure (h : M.IsFan F b c)
    (hcl : F[0] ∈ (M.bDual (!b)).closure {x | x ∈ F.tail}) : M.eConn {e | e ∈ F} ≤ 1 := by
  cases h with
  | of_pair b e f he hf hne =>
    grw [← eConn_bDual M (!b), eConn_le_eRk, show {x | x ∈ [e, f]} = {e, f} by grind,
      eRk_insert_of_mem_closure (by simpa using hcl), eRk_singleton_le]
  | cons_triangle e x y F b c h heF hT =>
    have hcl' : e ∈ (M.bDual (!b)).closure {z | z ∈ x :: y :: F} :=
      mem_of_mem_of_subset hT.mem_closure₁ <| closure_subset_closure _ <| by grind
    grw [← ENat.add_one_le_add_one_iff, ← eConn_bDual M !b, one_add_one_eq_two,
      ← (h.bDual !b).eConn_le_two,
      ← (M.bDual !b).eConn_insert_add_one_eq hcl' (by simpa using hcl) (by grind)]
    convert rfl.le
    grind

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
