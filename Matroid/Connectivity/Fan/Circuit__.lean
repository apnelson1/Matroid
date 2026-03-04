import Matroid.Connectivity.Fan.Basic
import Matroid.Connectivity.Separation.Vertical
import Mathlib.Data.ZMod.Basic

open Set List



set_option linter.style.longLine false

variable {α : Type*} {M : Matroid α} {X Y C K T : Set α} {e f g x y : α} {b c d : Bool}
    {J : Bool → List α} {L : List α} {n i j : ℕ} {F J : List α} {b c : Bool} {L : List ℕ}


def List.valsBetween (L : List α) (p q : ℕ) (b : Bool) : Set α :=
    {x | ∃ (i : ℕ) (hi : i < L.length), p < i ∧ i < q ∧ i.bodd = b ∧ L[i] = x}

lemma List.valsBetween_subset (L : List α) p q b : L.valsBetween p q b ⊆ {e | e ∈ L} := by
  grind [List.valsBetween]

lemma List.valsBetween_self (L : List α) p b : L.valsBetween p p b = ∅ := by
  grind [List.valsBetween]

lemma valsBetween_add_two (L : List α) {p q : ℕ} (hpq : p < q + 1) (hq : q.bodd = !b)
    (hqn : q + 1 < L.length) :
    L.valsBetween p (q + 2) b = insert L[q + 1] (L.valsBetween p q b) := by
  refine subset_antisymm ?_ <| insert_subset ⟨q + 1, hqn, hpq, by lia, by simpa, rfl⟩ ?_
  · rintro _ ⟨i, hi, hpi, hiq, rfl, rfl⟩
    by_cases hi : i < q
    · exact .inr ⟨i, by grind⟩
    grind
  grind [List.valsBetween]

namespace Matroid

lemma IsFan.getElem_mem_valsBetween_iff {p q d} (hF : M.IsFan F b c) {hi : i < F.length} :
    F[i] ∈ F.valsBetween p q d ↔ p < i ∧ i < q ∧ i.bodd = d := by
  simp only [valsBetween, exists_and_left, mem_setOf_eq]
  grind [hF.getElem_inj_iff]

lemma IsFan.isCircuit_interval (hF : M.IsFan F b c) (h0i : 0 < i) (hij : i < j)
    (hjF : j + 1 < F.length) (hib : i.bodd = b) (hjb : j.bodd = b) :
    M.IsCircuit <| insert F[i] (insert F[j] (F.valsBetween i j (!b))) := by
  obtain ⟨d, hd, rfl⟩ : ∃ d, j = i + 2 * d + 2 := by
    subst hib
    obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hij
    cases hd : d.bodd; simp [hd] at hjb
    exact ⟨d.div2, by grind [d.bodd_add_div2]⟩
  induction d with
  | zero =>
    simp only [mul_zero, add_zero]
    rw [valsBetween_add_two _ (by lia) (by simpa) (by lia), valsBetween_self, insert_empty_eq]
    exact (hF.isTriangle_getElem_of_eq (i := i) (by lia) hib).swap_right.isCircuit
  | succ d ih =>
    -- inductively, the set `C₀ = {i, i + 1, i + 3, ..., i + 2d + 1, i + 2d + 2}` is a circuit.
    specialize ih (by lia) (by lia) (by simpa)
    -- let `T` be the triangle starting with `i + 2 d + 2`.
    have hT := hF.isTriangle_getElem_of_eq (i := i + 2 * d + 2) (by lia) (by simpa)
    -- choose a circuit `C` containing `F i` and contained in `C ∪ T - F i`.
    obtain ⟨C, hCss, hC, hiC⟩ :=
      ih.strong_elimination hT.isCircuit (e := F[i + 2 * d + 2]) (f := F[i])
      (by simp) (by simp) (by simp) (by simp [hF.nodup.getElem_inj_iff, add_assoc])
    convert hC
    -- rw [valsBetween_add_two _ (by lia) (by simpa) (by lia)]
    refine (hCss.trans ?_).antisymm' <| insert_subset hiC ?_
    · nth_rw 2 [valsBetween_add_two _ (by lia) (by simpa) (by lia)]
      grind
    suffices aux : ∀ x ≤ d + 1, F.valsBetween i (i + 2 * x + 2) (!b) ⊆ C
    · refine insert_subset ?_ (aux _ rfl.le)
      have hK := hF.isTriad_getElem_of_eq (i + 2 * (d + 1) + 1) (by lia) (by simpa)
      have h_or := hK.mem_or_mem_of_isCocircuit (K := C) (by simpa)
        (aux _ rfl.le ?_)
      · rwa [or_iff_left] at h_or
        refine notMem_subset hCss ?_
        simp [hF.nodup.getElem_inj_iff, add_assoc, mul_add, hF.getElem_mem_valsBetween_iff]
      simpa [hF.getElem_mem_valsBetween_iff]
    intro x hx
    induction x with
    | zero =>
      rw [valsBetween_add_two _ (by lia) (by simpa) (by lia), valsBetween_self, insert_empty_eq]
      obtain rfl | i := i; simp at h0i
      have hT := hF.isTriad_getElem_of_eq i (by lia) (by simpa using hib)
      obtain hi | hi2 := hT.swap_left.mem_or_mem_of_isCocircuit (by simpa) hiC
      · simpa [hF.nodup.getElem_inj_iff, hF.getElem_mem_valsBetween_iff, add_assoc] using hCss hi
      simpa [add_assoc]
    | succ x ih =>
      rw [valsBetween_add_two _ (by lia) (by simpa) (by lia)]
      suffices F[i + 2 * x + 1 + 2] ∈ C by
        simpa [mul_add, ← add_assoc, insert_subset_iff, ih (by lia)]
      have hT := hF.isTriad_getElem_of_eq (i + 2 * x + 1) (by lia) (by simpa)
      rw [← hT.swap_left.mem_iff_mem_of_isCocircuit (by simpa)]
      · exact ih (by lia) <| by simpa [hF.getElem_mem_valsBetween_iff]
      refine notMem_subset hCss ?_
      suffices 2 * x = 2 * d + 1 ∨ 2 * x = 2 * d + 2 ∨ x = d → x = d by
        simpa [add_assoc, hF.nodup.getElem_inj_iff, hF.getElem_mem_valsBetween_iff, hib]
      lia


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

/-- For any odd-length fan `F = [a, b, ..., z]` in which `{a, b}` isn't a series pair,
there is a circuit `C` with `a ∈ C ∩ F ⊆ {a, z}`. -/
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

structure IsCyclicFan (M : Matroid α) (n : ℕ) (J : Bool → ZMod n → α) : Prop where
  isTriangle_bDual : ∀ b i, (M.bDual b).IsTriangle {J b i, J b (i + 1), J (!b) (i + b.toNat)}
  inj : ∀ b b' i i', J b i = J b' i' → i = i' ∧ b = b'

lemma IsCyclicFan.isTriangle {J} (h : M.IsCyclicFan n J) (i : ZMod n) :
    M.IsTriangle {J false i, J false (i + 1), J true i} := by
  simpa using h.isTriangle_bDual false i

lemma IsCyclicFan.isTriad {J} (h : M.IsCyclicFan n J) (i : ZMod n) :
    M.IsTriad {J true i, J true (i + 1), J false (i + 1)} := by
  simpa using h.isTriangle_bDual true i

structure IsCyclicFan' (M : Matroid α) (n : ℕ) (J : Bool → ZMod n → α) : Prop where
  isTriangle : ∀ i, M.IsTriangle {J false i, J false (i + 1), J true i}
  isTriad : ∀ i, M.IsTriad {J true i, J true (i + 1), J false (i + 1)}
  inj : ∀ b b' i i', J b i = J b' i' → i = i' ∧ b = b'

lemma IsCyclicFan.neg {J} (h : M.IsCyclicFan n J) :
    M.IsCyclicFan n (fun b i ↦ J b (- b.toNat - i)) := by
  refine ⟨fun b i ↦ ?_, by grind [h.inj]⟩
  have hwin := insert_comm .. ▸ h.isTriangle_bDual b (- 1 - b.toNat - i)
  cases b
  · simpa [sub_add_eq_add_sub, sub_eq_add_neg] using hwin
  simpa [sub_add_eq_add_sub, ← sub_sub, show - i - 1 = - 1 - i by ring,
    show - 1 - i - 1 = -1 - 1 - i by ring] using hwin

lemma IsCyclicFan.dual_neg {J} (h : M.IsCyclicFan n J) :
    M✶.IsCyclicFan n (fun b i ↦ J (!b) (- i)) := by
  refine ⟨fun b i ↦ ?_, by grind [h.inj]⟩
  have hwin := bDual_dual .. ▸ insert_comm .. ▸ h.isTriangle_bDual (!b) ((- 1) + (- i))
  simp_rw [← singleton_union] at hwin ⊢
  convert hwin using 4
  · ring
  · simp
  cases b with simp

lemma IsCyclicFan.add {J} (h : M.IsCyclicFan n J) (d : ZMod n) :
    M.IsCyclicFan n (fun b i ↦ J b (i + d)) :=
  ⟨fun b i ↦ by simpa [add_right_comm] using h.isTriangle_bDual b (i + d), by grind [h.inj]⟩

lemma IsCyclicFan.dual {J} (h : M.IsCyclicFan n J) :
    M✶.IsCyclicFan n (fun b i ↦ J (!b) (i + b.toNat)) :=
  ⟨fun b i ↦ by simpa [add_right_comm] using h.isTriangle_bDual (!b) (i + b.toNat),
    fun b b' i i' h_eq ↦ by grind [h.inj]⟩

lemma IsCyclicFan.dual_sub {J} (h : M.IsCyclicFan n J) :
    M✶.IsCyclicFan n (fun b i ↦ J (!b) (i - (!b).toNat)) := by
  refine ⟨fun b i ↦ ?_, fun b b' i i' h_eq ↦ by grind [h.inj]⟩
  cases b
  · simpa using h.isTriad (i - 1)
  simpa using h.isTriangle i

lemma isCyclicFan_aux_lt {F : List α} (hn : 2 ≤ n) (hF : 2 * n = F.length) {i : ZMod n} {d : Bool} :
    2 * i.val + d.toNat < F.length := by
  grind [Nat.add_one_le_of_lt <| @ZMod.val_lt _ (NeZero.of_gt hn) i]

lemma isCyclicFan_aux_inj {n : ℕ} (hn : 2 ≤ n) {i i' : ZMod n} {d d' : Bool}
    (h_eq : 2 * i.val + d.toNat = 2 * i'.val + d'.toNat) :
    i = i' ∧ d = d' := by
  have := NeZero.of_gt (show 1 < n from hn)
  obtain rfl | rfl := d.eq_or_eq_not d'
  · exact ⟨(ZMod.val_injective (n := n)) (by simpa using h_eq), rfl⟩
  cases d' with grind

/-- If `F` is a fan on the entire ground set that starts with a joint, then `F` determines
a cyclic fan. We insist that `F` starts with a joint so that the description of the cyclic
fan doesn't involve wrapping indices around. -/
lemma IsFan.isCyclicFan_of_ground_eq (hF : M.IsFan F false c) (hM : M.Simple) (hM' : M✶.Simple)
    (hFE : {e | e ∈ F} = M.E) : ∃ (n : ℕ) (hn : 2 ≤ n) (hnF : 2 * n = F.length), M.IsCyclicFan n <|
    fun d i ↦ F[2 * i.val + d.toNat]'(isCyclicFan_aux_lt hn hnF) := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' <| hF.length_ge_four_of_eq_ground hFE
  obtain ⟨hml, ht⟩ := hF.isTriangle_bDual_of_simple (n := m + 2) (by lia) hM hM' hFE
  rw [hm, even_iff_exists_two_mul] at hml
  obtain ⟨n, hmn⟩ := hml
  have hn1 : Fact (1 < n) := ⟨by grind⟩
  refine ⟨n, by lia, by lia, fun d i ↦ ?_, fun d d' i i' h ↦ ?_⟩
  · obtain hin | hin := (show i.val + 1 ≤ n from i.val_lt).eq_or_lt
    · have hi1 : (i + 1).val = 0 := by simp [ZMod.val_add, ZMod.val_one, hin]
      cases d
      · simp only [bDual_false, show 2 * i.val = m + 2 by lia, Bool.toNat_false, add_zero, hi1,
          mul_zero, Nat.cast_zero, Bool.not_false, Bool.toNat_true]
        rwa [pair_comm]
      simp only [bDual_true, Bool.toNat_true, hi1, mul_zero, zero_add, Nat.cast_one, Bool.not_true,
        Bool.toNat_false, add_zero, dual_isTriangle_iff, show 2 * i.val + 1 = m + 3 by lia]
      obtain rfl : c = true := by simpa [hm, hmn, Nat.bodd_two] using hF.length_bodd_eq
      refine (IsTriangle.rotate_left ?_).rotate_left
      simpa [hm] using
        (hF.reverse.isTriangle_bDual_of_simple (n := m + 2) (by simpa) hM hM' (by simpa)).2
    have hrw : (i + 1).val = i.val + 1 := by
      rw [ZMod.val_add_of_lt (by simpa [ZMod.val_one]), ZMod.val_one]
    have hwin := pair_comm .. ▸ hF.isTriangle_getElem (i := 2 * i.val + d.toNat) (by grind)
    cases d with simp_all [mul_add]
  exact isCyclicFan_aux_inj (by lia) (by rwa [hF.getElem_inj_iff] at h)

/-- Any fan on the ground set of a simple, cosimple matroid is a cyclic fan. -/
lemma IsFan.exists_isCyclicFan_of_ground_eq (hF : M.IsFan F b c) (hM : M.Simple) (hM' : M✶.Simple)
    (hFE : {e | e ∈ F} = M.E) : ∃ n J, 2 * n = F.length ∧ M.IsCyclicFan n J := by
  obtain ⟨m, hm⟩ := Nat.exists_eq_add_of_le' <| hF.length_ge_four_of_eq_ground hFE
  cases b
  · obtain ⟨n, hn, hnF, h⟩ := hF.isCyclicFan_of_ground_eq hM hM' hFE
    exact ⟨n, _, hnF, h⟩
  obtain ⟨n, hn, hnF, h⟩ := hF.dual.isCyclicFan_of_ground_eq hM' (by simpa) hFE
  exact ⟨n, _, hnF, M.dual_dual ▸ h.dual⟩

/-- Every cyclic fan gives a fan. -/
lemma IsCyclicFan.isFan {J} (hn : 2 ≤ n) (h : M.IsCyclicFan n J) :
    M.IsFan ((List.range (2 * n)).map fun i ↦ J i.bodd i.div2) false true := by
  refine isFan_of_eq_of_forall_triangle (by grind) ?_ (by simp) ?_
  · simp [nodup_iff_getElem?_ne_getElem?]
    intro i j hlt hj h_eq
    rw [getElem?_eq_getElem (by grind), getElem?_eq_getElem (by grind)] at h_eq
    simp only [getElem_range, Option.map_some, Option.some.injEq] at h_eq
    obtain ⟨hij, hij'⟩ := h.inj _ _ _ _ h_eq
    rw [ZMod.natCast_eq_natCast_iff] at hij
    grind [i.bodd_add_div2, j.bodd_add_div2, hij.eq_of_lt_of_lt]
  simp only [length_map, length_range, Bool.false_bne, getElem_map, getElem_range, Nat.bodd_succ,
    Nat.div2_succ, Nat.succ_eq_add_one, Bool.not_not, Bool.cond_not]
  intro i hi
  cases hd : i.bodd
  · simpa [hd, pair_comm (J true _)] using h.isTriangle_bDual i.bodd i.div2
  simpa [hd, pair_comm (J false _)] using h.isTriangle_bDual i.bodd i.div2
