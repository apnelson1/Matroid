module

public import Matroid.Connectivity.WIP.Joints
public import Matroid.Connectivity.Triangle
public import Matroid.Connectivity.Separation.Vertical
public import Matroid.ForMathlib.List.Set

open Set List Bool

set_option linter.style.longLine false

variable {α : Type*} {M : Matroid α} {X Y C K T : Set α} {e f g x y : α} {b c d : Bool}
    {n i j p q r : ℕ} {b c : Bool} {F : M.Fan}

namespace Matroid.Fan

-- lemma foo (F : M.Fan) (i C) (hi : i < (F.joints false).length)
--     (hiC : (F.joints false)[i] ∈ C) (hC : M.IsCircuit C) :
--     (F.joints true)[i] ∈ C ∨ (F.joints true)[i + 1] ∈ C :=
--   (F.isTriangle_bDual_joints true i (by grind)).swap_left.mem_or_mem_of_isCircuit_bDual
--     (K := C) (by simpa) (by simpa)


-- /-- If a circuit contains a joint, it contains the cojoint before or after.
-- In this version, the fan starts with a cojoint. -/
-- lemma mem_or_mem_cojoint_of_mem (F : M.Fan b c) (i C)
--     (hi : i + (b != c).toNat < (F.joints (!b)).length)
--     (hiC : (F.joints (!b))[i] ∈ C) (hC : (M.bDual (!b)).IsCircuit C) :
--     (F.joints b)[i] ∈ C ∨ (F.joints b)[i + 1] ∈ C :=
--   (F.isTriangle_bDual_joints b i (by grind)).swap_left.mem_or_mem_of_isCircuit_bDual hC (by simpa)

-- /-- If a circuit contains a joint, it contains the cojoint before or after.
-- In this version, the fan starts with a joint. -/
-- lemma mem_or_mem_cojoint_of_add_one_mem (F : M.Fan b c) (i C)
--     (hi : i + 1 + (b == c).toNat < (F.joints b).length) (hiC : (F.joints b)[i + 1] ∈ C)
--     (hC : (M.bDual b).IsCircuit C) :
--     (F.joints (!b))[i]'(by cases b with grind) ∈ C ∨
--     (F.joints (!b))[i + 1]'(by cases b with grind) ∈ C :=
--   (F.isTriangle_bDual_joints (!b) i (by cases b with grind)).swap_left.mem_or_mem_of_isCircuit_bDual
--     (by simpa using hC) (by simpa)



-- lemma mem_iff_mem₁₂ (F : M.Fan b c) (i C) (hi : i + 2 < F.length)
--     (hC : (M.bDual (i.bodd == b)).IsCircuit C) (heC : F[i] ∉ C) : F[i + 1] ∈ C ↔ F[i + 2] ∈ C := by
--   rw [(F.isTriangle i hi).mem_iff_mem_of_isCircuit_bDual _ heC]
--   obtain rfl | rfl := b.eq_or_eq_not i.bodd
--   <;> simpa using hC

-- lemma mem_iff_mem₀₂ (F : M.Fan b c) (i C) (hi : i + 2 < F.length)
--     (hC : (M.bDual (i.bodd == b)).IsCircuit C) (heC : F[i + 1] ∉ C) : F[i] ∈ C ↔ F[i + 2] ∈ C := by
--   refine (F.isTriangle i hi).swap_left.mem_iff_mem_of_isCircuit_bDual ?_ heC
--   obtain rfl | rfl := b.eq_or_eq_not i.bodd
--   <;> simpa using hC

-- lemma mem_iff_mem₀₁ (F : M.Fan b c) (i C) (hi : i + 2 < F.length)
--     (hC : (M.bDual (i.bodd == b)).IsCircuit C) (heC : F[i + 2] ∉ C) : F[i] ∈ C ↔ F[i + 1] ∈ C := by
--   rw [(F.isTriangle i hi).reverse.mem_iff_mem_of_isCircuit_bDual ?_ heC]
--   obtain rfl | rfl := b.eq_or_eq_not i.bodd
--   <;> simpa using hC

-- lemma mem_or_mem₀₁ (F : M.Fan b c) (i C) (hi : i + 2 < F.length)
--     (hC : (M.bDual (i.bodd == b)).IsCircuit C) (heC : F[i + 2] ∈ C) : F[i] ∈ C ∨ F[i + 1] ∈ C := by
--   refine (F.isTriangle i hi).reverse.swap_right.mem_or_mem_of_isCircuit_bDual ?_ heC
--   obtain rfl | rfl := b.eq_or_eq_not i.bodd
--   <;> simpa using hC

-- lemma mem_or_mem₀₂ (F : M.Fan b c) (i C) (hi : i + 2 < F.length)
--     (hC : (M.bDual (i.bodd == b)).IsCircuit C) (heC : F[i + 1] ∈ C) : F[i] ∈ C ∨ F[i + 2] ∈ C := by
--   refine (F.isTriangle i hi).swap_left.mem_or_mem_of_isCircuit_bDual ?_ heC
--   obtain rfl | rfl := b.eq_or_eq_not i.bodd
--   <;> simpa using hC

-- lemma mem_or_mem₁₂ (F : M.Fan b c) (i C) (hi : i + 2 < F.length)
--     (hC : (M.bDual (i.bodd == b)).IsCircuit C) (heC : F[i] ∈ C) : F[i + 1] ∈ C ∨ F[i + 2] ∈ C := by
--   refine (F.isTriangle i hi).mem_or_mem_of_isCircuit_bDual ?_ heC
--   obtain rfl | rfl := b.eq_or_eq_not i.bodd
--   <;> simpa using hC

lemma getElems_Ico_subset_closure (F : M.Fan) (hp : p.bodd = F.b) (hq : q.bodd = !F.b)
    (hqF : q ≤ F.length) : {e | e ∈ (F : List α).extract p q} ⊆
      M.closure {e | e ∈ ((F : List α).extract p q) ∧ e ∈ (F.joints false)} := by
  obtain hpq | hpq := le_or_gt q p
  · simp [extract_eq_nil _ hpq]
  simp_rw [Set.subset_def, mem_extract_iff_getElem]
  rintro _ ⟨i, hi, hpi, hiq, rfl⟩
  obtain hb | hb := F.b.eq_or_eq_not i.bodd
  · exact mem_closure_of_mem' _ (by simp [hpi, hiq, hi, getElem_mem_joints_iff, hb]) (by simp)
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
  simp [pair_subset_iff, getElem_mem_joints_iff, hb, show p ≤ i by lia, show i < q by lia,
    show p ≤ i + 2 by lia, show i + 2 < q by lia, show i + 2 < F.length by lia,
    show i < F.length by lia]

lemma joints_indep (F : M.Fan) (h_pair : F.b = false → F.c = false → ¬ M.Parallel F[0] F.getLast) :
    M.Indep ({e | e ∈ F.joints false}) := by
  induction hn : F.length using Nat.strong_induction_on generalizing F M with | h n ih =>
  wlog h : F.b = false → F.c = false generalizing F with aux
  · simp only [Classical.not_imp, not_eq_false] at h
    simpa using aux F.reverse (fun hb hc h ↦ h_pair hc hb <| by simpa using h.symm) (by simpa)
      (by simp [h.1])
  by_cases h2 : F.length ≤ 2
  · obtain ⟨e, f, b, he, hf, hef, rfl⟩ := eq_of_length_le_two h2
    cases b with
    | false => simpa using he false
    | true => simpa [ofPair_joints] using hf false
  cases hb : F.b with
  | true =>
    have hpara : F.c = false → ¬ M.Parallel F[1] F.getLast := by
      intro hc hpara
      grind [show 1 = F.length ∨ 2 = F.length ∨ 3 = F.length by
        simpa using (F.isTriangle_bDual_of_eq 0 true (by lia)
          (by simpa)).isCircuit.mem_iff_mem_of_parallel_bDual hpara]
    have hwin := ih (F.tail (by lia)).length (by grind) (F.tail (by lia)) (by simpa [hb]) rfl
    simpa [tail_joints, hb] using hwin
  | false =>
  specialize ih (F.length - 1) (by lia) (F.contractHead (by lia) (by simp [hb]) h_pair)
  replace ih : (M ／ {F[0]}).Indep {e | e ∈ (F.tail (by lia)).joints false} := by
    simpa [length_tail, hb] using ih
  rw [F.eq_tail_cons (by lia), cons_joints, cond_neg (by simp [hb]), List.toSet_cons_eq]
  rw [F.isNonloop.contractElem_indep_iff] at ih
  exact ih.2

lemma indep_of_subset_joints (F : M.Fan) {I} (hI : I ⊆ {e | e ∈ F.joints false})
    (hpq : F.b = false → F.c = false → F[0] ∈ I → F.getLast ∈ I → ¬ M.Parallel F[0] F.getLast) :
    M.Indep I := by
  by_cases! hdg : F.b = false → F.c = false → ¬ M.Parallel F[0] F.getLast
  · exact (F.joints_indep hdg).subset hI
  obtain ⟨hb, hc, hpara⟩ := hdg
  obtain h0 | hlast : F[0] ∉ I ∨ F.getLast ∉ I := by tauto
  · refine ((F.tail (by grind)).joints_indep (by simp [hb])).subset ?_
    rwa [tail_joints, cond_pos (by simp [hb]), F.joints_nodup.toSet_tail_eq (by simp),
      subset_sdiff_singleton_iff, ← getElem_zero F.length_joints_pos, joints_getElem_zero,
      Bool.cond_pos (by simp [hb]),and_iff_left h0]
  refine ((F.dropLast (by grind)).joints_indep (by simp [hc])).subset ?_
  rwa [dropLast_joints, cond_pos (by simp [hc]),
    F.joints_nodup.toSet_dropLast_eq (by simp), subset_sdiff_singleton_iff,
    joints_getLast, Bool.cond_pos (by simp [hc]), and_iff_left hlast]

lemma joints_extract_indep (F : M.Fan)
    (hpq : p = 0 → (F.joints false).length ≤ q → F.b = false → F.c = false →
      ¬ M.Parallel F[0] F.getLast) : M.Indep {e | e ∈ (F.joints false).extract p q} := by
  refine F.indep_of_subset_joints (extract_isInfix ..).subset fun hb hc h1 h2 ↦ hpq ?_ ?_ hb hc
  · by_contra hcon
    simp [mem_extract_iff_getElem, joints_getElem, hb, hcon] at h1
  simp only [extract_eq_take_drop, mem_extract_iff_getElem, joints_getElem, hb, bne_self_eq_false,
    toNat_false, mem_ofPred_eq, getElem_eq_getLast_iff] at h2
  grind

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
  grw [← joints_subset (d := F.b), Indep.eRk_eq_encard, F.joints_nodup.encard_toSet_eq,
    length_joints, beq_self_eq_true, toNat_true, show (2 : ℕ∞) = (2 : ℕ) from rfl, ← Nat.cast_mul,
    Nat.two_mul_div2 _ (by simpa), Nat.cast_add, Nat.cast_one]
  simpa using (F.bDual F.b).joints_indep <| by simpa [F.right_eq_left hF]

lemma isCircuit_intervalC (F : M.Fan) (hpq : p < q) (hqF : q < F.length)
    (hpb : p.bodd = F.b) (hqb : q.bodd = F.b)
    (hdg : F.b = false → F.c = false → p = 0 → q + 1 = F.length → ¬ M.Parallel F[0] F.getLast) :
    M.IsCircuit <| {e | e ∈ F.intervalC p q false hpq hqF (by simpa) (by simpa)} := by
  induction q using Nat.strong_induction_on with | h q ih =>
  obtain ⟨q, hqlt, rfl, rfl | hlt⟩ : ∃ q' < q, q' + 2 = q ∧ (q' = p ∨ p < q') := by
    obtain ⟨rfl | rfl | d, rfl⟩ := exists_add_of_le hpq.le
    · lia
    · simp [hpb] at hqb
    exact ⟨p + d, by grind⟩
  ·
  sorry

/-- Let `F[p]` and `F[q]` be joints of a fan, and `K` be the set of cojoints between `p` and `q`.
If `F[p]` and `F[q]` are not parallel and at the beginning and the end of the fan,
then `{F[p], F[q]} ∪ K` is a circuit.

The nondegeracy hypothesis has some redundancy, since `i = 0` and `q + 1 = F.length` implies that
`b = c = false`; we include it so it is easier to discharge quickly in various cases.  -/
lemma IsFan.isCircuit_interval (F : M.Fan b c) (hpq : p < q) (hqF : q < F.length)
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

lemma Fan.eq_interval_of_notMem_mem_mem (F : M.Fan) (hpq : p + 1 < q)
    (hqF : q < (F.joints false).length) ()

    -- (hpb : p.bodd = !F.b) (hqb : q.bodd = F.b)
    -- (hC : M.IsCircuit C)
    -- (hpC : F[p] ∉ C) (hp1C : F[p + 1] ∈ C) (hqC : F[q] ∈ C) :
    -- C = insert F[p + 1] (insert F[q] <| {e | e ∈ (F : List α).extract p q ∧ })

lemma Fan.eq_interval_of_notMem_mem_mem (F : M.Fan) (hpq : p + 1 < q)
    (hqF : q < F.length) (hpb : p.bodd = !F.b) (hqb : q.bodd = F.b) (hC : M.IsCircuit C)
    (hpC : F[p] ∉ C) (hp1C : F[p + 1] ∈ C) (hqC : F[q] ∈ C) :
    C = insert F[p + 1] (insert F[q] <| {e | e ∈ (F : List α).extract p q ∧ })

    -- C = (F.getElems (insert (p + 1) <| insert q <| {i ∈ Ico (p + 1) q | i.bodd = !b})) := by

/-- If a circuit of a matroid contains joints `F[p + 1], F[q]` of a fan `F`,
and does not contain the cojoint `F[p]`,
then it comprises precisely `F[p + 1], F[q]`, and the cojoints between them.  -/
lemma IsFan.eq_interval_of_notMem_mem_mem (F : M.Fan b c) (hpq : p + 1 < q)
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

lemma IsFan.exists_eq_interval_of_notMem_mem_add_one (F : M.Fan b c) (hpq : p + 1 < q)
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
lemma IsFan.exists_eq_interval_of_notMem_mem_notMem {s t r : ℕ} (F : M.Fan b c) (hsr : s < r)
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

-- lemma IsFan.delete_head'' (F : M.Fan b c) (h3 : 3 ≤ F.length)
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

lemma IsFan.delete_head (F : M.Fan true c) (h3 : 3 ≤ F.length)
    (h_pair : c = true → ¬ M✶.Parallel F[0] F[F.length - 1]) :
    (M ＼ {F[0]}).IsFan F.tail false c := by
  simpa using (hF.dual.contract_head h3 (by simpa)).dual

lemma IsFan.contract_head_three (F : M.Fan b c) (h3 : F.length = 3)
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
lemma IsFan.length_ge_four_of_eq_ground [M.Simple] [M✶.Simple] (F : M.Fan b c)
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
lemma IsFan.exists_isCircuit_subset_first_last (F : M.Fan false false)
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
lemma IsFan.exists_isCircuit_first_mem_of_length_odd (F : M.Fan false c)
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
