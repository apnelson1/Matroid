import Matroid.Connectivity.Fan.Basic
import Matroid.Connectivity.Separation.Vertical
import Mathlib.Tactic.DepRewrite


open Set List



set_option linter.style.longLine false

variable {α : Type*} {M : Matroid α} {X Y C K T : Set α} {e f g x y : α} {b c d : Bool}
    {J : Bool → List α} {L : List α} {n i j p q r : ℕ} {F J : List α} {b c : Bool}

/-- Take all the elements `L[i]` where `i ≤ p < q`, and `i` has a given parity. -/
def List.altBetween (L : List α) (p q : ℕ) (b : Bool) : Set α :=
    {x | ∃ (i : ℕ) (hi : i < L.length), p ≤ i ∧ i < q ∧ i.bodd = b ∧ L[i] = x}

lemma List.altBetween_subset_iff : L.altBetween p q b ⊆ X ↔
    ∀ i (hi : i < L.length), p ≤ i → i < q → i.bodd = b → L[i] ∈ X := by
  grind [List.altBetween]

lemma List.altBetween_subset (L : List α) p q b : L.altBetween p q b ⊆ {e | e ∈ L} := by
  grind [List.altBetween]

@[simp]
lemma List.altBetween_self : L.altBetween p p b = ∅ := by
  grind [List.altBetween]

lemma altBetween_mono {p q p' q'} (L : List α) (hpp' : p ≤ p') (hqq' : q' ≤ q) (b : Bool) :
    L.altBetween p' q' b ⊆ L.altBetween p q b := by
  grind [altBetween]

lemma altBetween_add_one_eq_self (p : ℕ) (hq : q.bodd = !b) :
    L.altBetween p (q + 1) b = L.altBetween p q b := by
  refine (altBetween_mono _ rfl.le (by lia) _).antisymm' ?_
  rintro x ⟨i, hi, hpi, hiq, rfl, rfl⟩
  refine ⟨i, hi, hpi, ?_, rfl, rfl⟩
  suffices i ≠ q by grind
  grind

lemma altBetween_add_one_left_eq_self (hqb : p.bodd = !b) (q : ℕ) :
    L.altBetween (p + 1) q b = L.altBetween p q b := by
  refine (altBetween_mono _ (by lia) rfl.le _).antisymm ?_
  rintro x ⟨i, hi, hpi, hiq, rfl, rfl⟩
  refine ⟨i, hi, ?_, hiq, rfl, rfl⟩
  suffices i ≠ p by grind
  grind

lemma altBetween_eq_insert_altBetween_add_one_left (hpq : p < q) (hp : p < L.length)
    (hqb : p.bodd = b) : L.altBetween p q b = insert L[p] (L.altBetween (p + 1) q b) := by
  refine subset_antisymm ?_ <| insert_subset ⟨p, by grind⟩ <| altBetween_mono _ (by lia) rfl.le _
  rintro _ ⟨i, hi, hpi, hiq, rfl, rfl⟩
  obtain rfl | hlt := hpi.eq_or_lt
  · simp
  exact .inr ⟨i, by grind⟩

lemma altBetween_add_one_eq_insert (hpq : p ≤ q) (hqlt : q < L.length) (hqb : q.bodd = b) :
    L.altBetween p (q + 1) b = insert L[q] (L.altBetween p q b) := by
  refine (insert_subset ?_ (altBetween_mono _ rfl.le (by lia) _)).antisymm' ?_
  · exact ⟨q, hqlt, hpq, by lia, hqb, rfl⟩
  rintro x ⟨i, hi, hpi, hiq, rfl, rfl⟩
  obtain rfl | hne := eq_or_ne i q
  · simp
  exact .inr ⟨i, hi, hpi, by grind, rfl, rfl⟩

lemma altBetween_union (L : List α) (hpq : p ≤ q) (hqr : q ≤ r) :
    L.altBetween p q b ∪ L.altBetween q r b = L.altBetween p r b := by
  apply (union_subset (altBetween_mono _ rfl.le hqr _) (altBetween_mono _ hpq rfl.le _)).antisymm
  rw [altBetween_subset_iff]
  rintro i hi hpi hir rfl
  obtain hle | hlt := lt_or_ge i q
  · exact .inl <| by use i, hi
  exact .inr <| by grind [altBetween]

lemma altBetween_add_two (hpq : p ≤ q) (hq : q.bodd = !b) (hqn : q + 1 < L.length) :
    L.altBetween p (q + 2) b = insert L[q + 1] (L.altBetween p q b) := by
  rw [altBetween_add_one_eq_insert (by lia) hqn (by simpa), altBetween_add_one_eq_self _ hq]

lemma List.Nodup.getElem_mem_altBetween_iff (hL : L.Nodup) {hi : i < L.length} :
    L[i] ∈ L.altBetween p q b ↔ p ≤ i ∧ i < q ∧ i.bodd = b := by
  simp only [altBetween, exists_and_left, mem_setOf_eq]
  grind [hL.getElem_inj_iff]

lemma getElem_mem_altBetween {hi : i < L.length} (hpi : p ≤ i) (hiq : i < q) (hib : i.bodd = b) :
    L[i] ∈ L.altBetween p q b := by
  grind [altBetween]

lemma altBetween_pair_eq_middle (hp : p + 1 < L.length) (hpb : p.bodd = !b) :
    L.altBetween p (p + 2) b = {L[p + 1]} := by
  rw [altBetween_add_two rfl.le hpb hp, altBetween_self, insert_empty_eq]

lemma altBetween_pair_eq_left (hp : p < L.length) (hpb : p.bodd = b) :
    L.altBetween p (p + 2) b = {L[p]} := by
  rw [altBetween_add_one_eq_self _ (by simpa), altBetween_add_one_eq_insert rfl.le hp hpb,
    altBetween_self, insert_empty_eq]

lemma altBetween_insert_drop_two {L : List α} {p q : ℕ} (hpq : p ≤ q)
    (hplt : p + 1 < L.length) (hp : p.bodd = !b) :
    insert L[p + 1] ((L.drop 2).altBetween p q b) = L.altBetween p (q + 2) b := by
  simp only [altBetween, getElem_drop, length_drop, exists_and_left, Set.ext_iff,
    Set.mem_insert_iff, mem_setOf_eq, iff_def, forall_exists_index, and_imp]
  refine fun i ↦ ⟨?_, ?_⟩
  · rintro (rfl | ⟨i, hpi, hiq, rfl, hilt, rfl⟩)
    · exact ⟨p + 1, by lia, by lia, by simpa, by lia, rfl⟩
    exact ⟨2 + i, by lia, by lia, by simp, by lia, rfl⟩
  rintro i hpi hiq rfl hlt rfl
  by_contra! hcon
  obtain rfl | rfl | i := i; grind; grind
  exact hcon.2 i (by lia) (by lia) (by simp) (by lia) (by grind)

lemma mem_extract_iff_getElem {L : List α} : x ∈ L.extract p q ↔ ∃ (i : ℕ) (hi : i < L.length),
    p ≤ i ∧ i < q ∧ L[i] = x := by
  simp only [extract_eq_drop_take, mem_take_iff_getElem, getElem_drop, length_drop, lt_inf_iff,
    exists_and_left]
  refine ⟨by grind, ?_⟩
  rintro ⟨i, hpi, hiq, hi, rfl⟩
  obtain ⟨d, rfl⟩ := exists_add_of_le hpi
  grind

lemma List.Nodup.getElem_mem_extract_iff (hL : L.Nodup) {hi : i < L.length} :
    L[i] ∈ L.extract p q ↔ p ≤ i ∧ i < q := by
  simp [mem_extract_iff_getElem, hL.getElem_inj_iff, hi]

lemma altBetween_subset_extract (L : List α) (p q : ℕ) (b : Bool) :
    L.altBetween p q b ⊆ {x | x ∈ L.extract p q} := by
  grind [altBetween, mem_extract_iff_getElem]

namespace Matroid

lemma IsFan.altBetween_subset_closure_altBetween (hF : M.IsFan F b c) (hi : i.bodd = b)
    (hj : j.bodd = b) (hj : j < F.length) :
    F.altBetween i (j + 1) (!b) ⊆ M.closure (F.altBetween i (j + 1) b) := by
  grw [← altBetween_add_one_left_eq_self (by simpa), altBetween_add_one_eq_self _ (by simpa),
    ← altBetween_add_one_eq_self (b := b) _ (by simpa)]
  rintro _ ⟨x, hx, hix, hxj, hxb, rfl⟩
  obtain rfl | x := x; lia
  grw [← altBetween_mono (p' := x) (q' := x + 3) _ (by lia) (by lia),
    altBetween_add_one_eq_insert (by simp) (by lia) (by simpa using hxb),
    altBetween_pair_eq_left (by lia) (by simpa using hxb), pair_comm]
  exact (hF.isTriangle_getElem_of_eq x (by lia) (by simpa using hxb)).mem_closure₂

lemma IsFan.altBetween_subset_closure_altBetween' (hF : M.IsFan F b c) (hj : j + 1 < F.length) :
    F.altBetween (i + 1) j (!b) ⊆ M.closure (F.altBetween i (j + 1) b) := by
  rintro _ ⟨x, hx, hix, hxj, hxb, rfl⟩
  have hne : i ≠ x := by rintro rfl; grind
  obtain rfl | x := x; grind
  grw [← altBetween_mono (p' := x) (q' := x + 3) _ (by lia) (by lia),
    altBetween_add_one_eq_insert (by lia) (by lia) (by simpa using hxb),
    altBetween_pair_eq_left (by lia) (by simpa using hxb), pair_comm]
  exact (hF.isTriangle_getElem_of_eq x (by lia) (by simpa using hxb)).mem_closure₂

lemma IsFan.extract_subset_closure_altBetween (hF : M.IsFan F b c)  (hi : i.bodd = b)
    (hj : j.bodd = b) (hjF : j < F.length) :
    {x | x ∈ F.extract i (j + 1)} ⊆ M.closure (F.altBetween i (j + 1) b) := by
  simp_rw [Set.subset_def, mem_extract_iff_getElem]
  simp only [Order.lt_add_one_iff, exists_and_left, mem_setOf_eq, forall_exists_index, and_imp]
  rintro e x hix hxj hlt rfl
  obtain rfl | rfl := b.eq_or_eq_not x.bodd
  · refine mem_closure_of_mem' _ ?_ (by grind)
    simp [hF.nodup.getElem_mem_altBetween_iff, hix, hxj]
  grw [← hF.altBetween_subset_closure_altBetween hi hj hjF, Bool.not_not,
    hF.nodup.getElem_mem_altBetween_iff]
  simp [hix, hxj]

/-- The joints are always independent, unless the first and last element are parallel joints. -/
lemma IsFan.joints_indep (hF : M.IsFan F b c)
    (h_pair : b = false → c = false → ¬ M.Parallel (F.head hF.ne_nil) (F.getLast hF.ne_nil)) :
    M.Indep {e | ∃ (i : ℕ) (hi : i < F.length), i.bodd = b ∧ F[i] = e} := by
  rw [indep_iff_forall_subset_not_isCircuit']
  simp only [exists_and_left, Set.subset_def, mem_setOf_eq, forall_exists_index, and_imp]
  refine ⟨fun C hFC hC ↦ ?_, by grind [hF.get_mem_ground]⟩
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le' hF.two_le_length
  have hodd : ∀ (i : ℕ) (hi : i < F.length), F[i] ∈ C → i.bodd = b := by grind
  have hcon : ∀ (i : ℕ) (hi : i < F.length), F[i] ∈ C → i = 0 ∨ i = n + 1 := by
    rintro (rfl | j) hj hiC; simp
    wlog hnj : j < n; grind
    obtain ⟨j', hj'b, hj', hj''⟩ := hFC _ hiC
    rw [hF.getElem_inj_iff] at hj''
    simp only [hj'', Nat.bodd_succ, Bool.not_eq_eq_eq_not] at hj'b
    rw [(hF.isTriangle_getElem j (by lia)).mem_iff_mem_of_isCircuit_bDual (K := C)
       (by simpa [hj'b])] at hiC
    · simpa [hj'b] using hodd _ _ hiC
    exact fun h' ↦ by simpa [hj'b] using hodd _ _ h'
  have hss : C ⊆ {F[0], F[n + 1]} := by grind
  have h0 := fun I ↦ ((hF.isNonloop (e := F[0]) (by simp))).indep.subset (I := I)
  have h1 := fun I ↦ ((hF.isNonloop (e := F[n + 1]) (by simp))).indep.subset (I := I)
  have h_eq : C = {F[0], F[n + 1]} := hss.eq_of_not_ssubset (by grind [hC.not_indep])
  obtain rfl : b = false := by simpa using hodd 0 (by lia) (by grind)
  have hnF : n.bodd = F.length.bodd := by simp [hn]
  obtain rfl : c = false := by simpa [hnF, hF.length_bodd_eq] using hodd (n + 1) (by lia) (by grind)
  refine h_pair rfl rfl ?_
  rw [parallel_iff_isCircuit (by grind), F.head_eq_getElem_zero, F.getLast_eq_getElem]
  simpa [hn, ← h_eq]

lemma IsFan.joints_indep' (hF : M.IsFan F b c)
    (h_pair : b = false → c = false → ¬ M.Parallel (F.head hF.ne_nil) (F.getLast hF.ne_nil)) :
    M.Indep (F.get '' {i | i.1.bodd = b}) := by
  convert hF.joints_indep h_pair
  refine Set.ext fun i ↦ ?_
  simp only [get_eq_getElem, mem_image, mem_setOf_eq, and_comm (a := _ = b)]
  constructor
  · rintro ⟨⟨x ,hx⟩, rfl, rfl⟩; grind
  rintro ⟨i, hi, rfl, rfl⟩
  use ⟨i, hi⟩

lemma IsFan.joints_indep'' (hF : M.IsFan F b c)
    (h_pair : b = false → c = false → ¬ M.Parallel (F.head hF.ne_nil) (F.getLast hF.ne_nil)) :
    M.Indep (F.altBetween 0 F.length b) := by
  convert hF.joints_indep h_pair
  grind [subset_antisymm_iff, altBetween]

/-- Let `F` be a fan whose first and last elements are not parallel joints.
If `i` and `j` are joints with `i < j`, and `K` is the set of cojoints between `i` and `j`,
then `{i, j} ∪ K` is a circuit -/
lemma IsFan.isCircuit_interval (hF : M.IsFan F b c)
    (hp : b = false → c = false → ¬ M.Parallel (F.head hF.ne_nil) (F.getLast hF.ne_nil))
    (hij : i < j) (hjF : j < F.length) (hib : i.bodd = b) (hjb : j.bodd = b) :
    M.IsCircuit <| insert F[i] (insert F[j] (F.altBetween i j (!b))) := by
  subst hib
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
  cases h : d.bodd
  · simp [h] at hjb
  rw [Nat.bodd_eq_odd, odd_iff_exists_bit1] at h
  obtain ⟨d, rfl⟩ := h
  induction d with
  | zero =>
    simp only [mul_zero, zero_add]
    rw [altBetween_pair_eq_middle (by lia) (by simp), pair_comm]
    exact (hF.isTriangle_getElem_of_eq i (by lia) rfl).isCircuit
  | succ d ih =>
    simp only [mul_add, mul_one, add_assoc, Nat.reduceAdd] at ⊢ ih
    simp_rw [← add_assoc] at ih
    specialize ih (by lia) (by lia) <| by cases h : i.bodd with simp [h, Nat.bodd_two]
    have hT := hF.isTriangle_getElem_of_eq (i + 2 * d + 2) (by lia) (by simp)
    convert ih.union_isCircuit_of_inter_eq_singleton hT.isCircuit (e := F[i + 2 * d + 2]) ?_
      (by simp) (by simp) ?_ using 1
    · simp_rw [show i + (2 * d + 4) = (i + 2 * d + 2) + 2 by ring]
      rw [altBetween_add_two (by lia) (by simp) (by lia), insert_comm (b := F[i + 2 * d + 2]),
        union_diff_distrib, insert_diff_self_of_notMem, insert_diff_self_of_notMem]
      · grind
      · simp [hF.nodup.getElem_inj_iff]
      simp [hF.nodup.getElem_inj_iff, hF.nodup.getElem_mem_altBetween_iff, add_assoc]
    · apply_fun (F[i] ∈ ·)
      simp [hF.nodup.getElem_inj_iff, add_assoc]
    set X1 := F.altBetween i.bodd.toNat (i + 2 * d + 3) i.bodd with hX1
    set X2 := F.altBetween (i + 2 * d + 2) (i + 2 * d + 5) i.bodd with hX2
    have hmod : M.IsModularPair X1 X2 := by
      refine Indep.isModularPair_of_union <| (hF.joints_indep'' hp).subset ?_
      apply union_subset <;> apply altBetween_mono <;> lia
    have hXconn : M.eLocalConn X1 X2 ≤ 1 := by
      grw [hmod.eLocalConn_eq_eRk_inter, eRk_le_encard]
      refine encard_le_one_iff_subsingleton.2 <|
        (subsingleton_singleton (a := F[i + 2 * d + 2])).anti ?_
      rintro _ ⟨⟨i1, hi1, -, hlt, hb, rfl⟩, ⟨i2, h_eq, hi2, -, hb', h'⟩⟩
      simp only [mem_singleton_iff, hF.nodup.getElem_inj_iff] at ⊢ h'
      grind
    grw [← hXconn, ← M.eLocalConn_closure_closure X1]
    refine M.eLocalConn_mono ?_ ?_
    · grw [hX1, ← hF.extract_subset_closure_altBetween (by simp) (by simp) (by lia)]
      simp_rw [insert_subset_iff, altBetween_subset_iff, mem_setOf_eq,
        hF.nodup.getElem_mem_extract_iff]
      grind
    grw [← hF.extract_subset_closure_altBetween (by simp) (by simp) (by lia)]
    simp_rw [insert_subset_iff, singleton_subset_iff, mem_setOf, hF.nodup.getElem_mem_extract_iff]
    grind

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

/-- For any odd-length fan `F = [a, b, ..., z]` in which `a` is a joint
and `{a, b}` isn't a series pair, there is a circuit `C` with `a ∈ C ∩ F ⊆ {a, z}`. -/
lemma IsFan.exists_isCircuit_first_mem_of_length_odd (hF : M.IsFan F false c)
    (h_odd : Odd F.length) (h01 : ¬ M✶.Parallel (F[0]'(by grind)) (F[1]'hF.two_le_length)) :
    ∃ C, M.IsCircuit C ∧ F[0]'(by grind) ∈ C ∧ ∀ i (hi : i + 1 < F.length),
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

-- lemma IsFan.interval_of_isCircuit (hF : M.IsFan F b c) (hC : M.IsCircuit C) (hCF : C ⊆ {e | e ∈ F})
--     (h0C : F.head hF.ne_nil ∉ C) (htail : F.getLast hF.ne_nil ∉ C) :
--     ∃ (i j : ℕ) (hij : i < j) (hj : j < F.length), i.bodd = b ∧ j.bodd = b ∧
--     C = insert F[i] (insert F[j] (F.altBetween i j (!b))) := by
--   sorry
