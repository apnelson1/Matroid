module

public import Matroid.Connectivity.WIP.Minor

set_option linter.style.longLine false

open Set List Bool


namespace Matroid.Fan

variable {α : Type*} {M : Matroid α} {X Y C K T : Set α} {e f g x y : α} {b b' c c' d : Bool}
    {n i j : ℕ} {J : List α} {F : M.Fan}

private lemma lt_aux (F : M.Fan) (d : Bool) (i : ℕ)
    (hi : i < (F.length + (F.b == d).toNat).div2) : 2 * i + (F.b != d).toNat < F.length := by
  rw [lt_div2_iff, Nat.lt_iff_add_one_le] at hi
  cases h : (F.b == d) with grind

/-- `F.joints d` is the sublist of elements of `F` that are in two `(M.bDual b)`-triangles of `F`.
We have `F[0] ∈ F.joints d` if and only if `d = F.b`, and otherwise `F[1] ∈ F.joints d`.  -/
def joints (F : M.Fan) (d : Bool) : List α := List.pmap
    (l := List.range (F.length + (F.b == d).toNat).div2)
    (P := fun (i : ℕ) ↦ i < (F.length + (F.b == d).toNat).div2)
    (f := fun i hi ↦ F[2 * i + (F.b != d).toNat]'(F.lt_aux d i (by simpa))) (by simp)

@[simp]
lemma joints_copy (F : M.Fan) {M' : Matroid α} {hM} : (F.copy M' hM).joints = F.joints := rfl

/-- Two fans with the same underlying lists and parity conditions have the same joints. -/
lemma joints_congr {M N : Matroid α} (F : M.Fan) (F' : N.Fan) (hF : (F : List α) = (F' : List α))
    {d d'} (hb : (F.b == d) = (F'.b == d')) : F.joints d = F'.joints d' := by
  simp_rw [joints, ← getElem_toList, ← hF, ← hb, show (F'.b != d') = (F.b != d) by grind,
    ← show F.length = F'.length by rw [← length_toList, hF]]
  exact pmap_congr_left (l := (List.range (F.length + (F.b == d).toNat).div2)) fun _ _ _ _ ↦ rfl

lemma joints_getElem (F : M.Fan) (d : Bool) (i : ℕ) {hi : i < (F.joints d).length} :
    (F.joints d)[i] = F[2 * i + (F.b != d).toNat]'(F.lt_aux d i <| by simpa [joints] using hi) := by
  simp [joints]

lemma length_joints (F : M.Fan) (d : Bool) :
    (F.joints d).length = (F.length + (F.b == d).toNat).div2 := by
  simp [joints]

lemma joints_subset (F : M.Fan) {d : Bool} : {e | e ∈ F.joints d} ⊆ F := by
  intro e he
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  simp [joints_getElem]

lemma joints_subset_ground (F : M.Fan) {d : Bool} : {e | e ∈ F.joints d} ⊆ M.E := by
  grw [joints_subset, F.subset_ground]

@[grind! .]
lemma two_mul_length_joints_of_even (F : M.Fan) (hbc : F.length.bodd = false) (d : Bool) :
    2 * (F.joints d).length = F.length := by
  rw [length_joints, Nat.add_div2, toNat_div2, add_zero, toNat_bodd, ← F.length.bodd_add_div2]
  simp [hbc]

@[grind! .]
lemma two_mul_length_joints_of_odd (F : M.Fan) (hbc : F.length.bodd = true) :
    2 * (F.joints F.b).length = F.length + 1 := by
  suffices 2 * (F.length.div2 + 1) = F.length + 1 by
    simpa [F.length_joints, hbc]
  nth_rw 1 [eq_comm, ← F.length.bodd_add_div2, hbc, Bool.toNat_true]
  lia

@[grind! .]
lemma two_mul_length_joints_add_one_of_odd (F : M.Fan) (hbc : F.length.bodd = true) :
    2 * (F.joints !F.b).length + 1 = F.length := by
  suffices 2 * F.length.div2 + 1 = F.length by simpa [F.length_joints]
  nth_rw 1 [eq_comm, ← F.length.bodd_add_div2, hbc, Bool.toNat_true, add_comm]

/-- In an even fan, there is the same number of both types of `joints`. -/
@[grind! .]
lemma length_joints_eq_length_joints (F : M.Fan) (hb : F.length.bodd = false) (d d' : Bool) :
    (F.joints d).length = (F.joints d').length := by
  rw [← Nat.mul_right_inj (a := 2) (by simp), two_mul_length_joints_of_even _ hb,
    two_mul_length_joints_of_even _ hb]

lemma getElem_mem_joints_iff {hi : i < F.length} : F[i] ∈ F.joints d ↔ i.bodd = (F.b != d) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨j, hj, hij⟩ := List.getElem_of_mem h
    obtain rfl : 2 * j + (F.b != d).toNat = i := by simpa [joints_getElem] using hij
    simp
  have hi_eq := h ▸ i.bodd_add_div2
  have := F.joints_getElem d i.div2 (hi := by grind [length_joints])
  simp_rw [add_comm, hi_eq] at this
  rw [← this]
  exact List.getElem_mem _

@[grind! .]
lemma length_joints_left_ge (F : M.Fan) : F.length ≤ 2 * (F.joints F.b).length := by
  grind [length_joints]

@[grind! .]
lemma length_joints_not_left_le (F : M.Fan) : 2 * (F.joints !F.b).length ≤ F.length := by
  rw [length_joints, beq_not_self]
  grind

@[grind! .]
lemma length_joints_right_ge (F : M.Fan) : F.length ≤ 2 * (F.joints F.c).length := by
  rw [← F.length.bodd_add_div2, length_joints,  ← F.length_bodd]
  grind

@[grind! .]
lemma length_joints_not_right_le (F : M.Fan) : 2 * (F.joints !F.c).length ≤ F.length := by
  rw [← F.length.bodd_add_div2, length_joints, show (F.b == !F.c) = !(F.b == F.c) by
    cases F.b with simp, ← F.length_bodd]
  cases h : F.length.bodd with simp [h]

@[grind! .]
lemma length_joints_le_length_joints_add_one (F : M.Fan) (d d' : Bool) :
    (F.joints d).length ≤ (F.joints d').length + 1 := by
  obtain rfl | rfl := d'.eq_or_eq_not d
  · simp
  grw [F.length_joints, F.length_joints]
  simp only [Nat.add_div2, toNat_div2, add_zero, toNat_bodd]
  obtain rfl | rfl := d.eq_or_eq_not F.b
  · simp [toNat_le_one]
  simp [add_assoc]

@[grind =>]
lemma lt_length_joints_of_lt_length_joints_add_one (F : M.Fan) (d' : Bool)
    (hi : i + 1 < (F.joints d).length) : i + (F.b != d).toNat < (F.joints d').length := by
  -- grw [← Nat.add_one_lt_add_one_iff, ← F.length_joints_le_length_joints_add_one d]
  obtain rfl | rfl := d.eq_or_eq_not d'
  · grind
  obtain hcb | hcb := F.c.eq_or_eq_not F.b
  · rw [← Nat.mul_lt_mul_left (show 0 < 2 by simp)] at ⊢ hi
    obtain rfl | rfl := d'.eq_or_eq_not F.c <;> grind
  grind

/-- Any joint is in a triangle with the next cojoint and the joint after that. -/
lemma isTriangle_bDual_joints (F : M.Fan) (d : Bool) (i : ℕ)
    (hi : i + 1 < (F.joints d).length) :
    ((M.bDual d).IsTriangle {(F.joints d)[i], (F.joints (!d))[i + (F.b != d).toNat]'
      (F.lt_length_joints_of_lt_length_joints_add_one (!d) hi), (F.joints d)[i + 1]}) := by
  simp only [joints_getElem]
  generalize_proofs h1 h2
  convert F.isTriangle (i := 2 * i + (F.b != d).toNat) (by lia) using 4
  · simp
  · rw [show (F.b != !d) = !(F.b != d) by simp]
    have hwin := (F.b != d).toNat_add_toNat_bnot
    lia
  grind

/-- Any joint is in a triad with the cojoints before and after it. This is the version where
the fan starts with a cojoint. -/
lemma isTriangle_bDual_cojoints (F : M.Fan) (i : ℕ)
    (hi : i + (F.b != F.c).toNat < (F.joints (!F.b)).length) :
    (M.bDual F.b).IsTriangle {(F.joints F.b)[i], (F.joints !F.b)[i], (F.joints F.b)[i + 1]} := by
  simpa using (F.isTriangle_bDual_joints F.b i (by grind))

/-- Any joint is in a triad with the cojoints before and after it. This is the version where
the fan starts with a joint. -/
lemma isTriangle_bDual_cojoints' (F : M.Fan) (i : ℕ)
    (hi : i + 1 + (F.b == F.c).toNat < (F.joints F.b).length) :
    (M.bDual (!F.b)).IsTriangle {(F.joints !F.b)[i]'(by cases h : F.b with grind),
      (F.joints F.b)[i + 1], (F.joints !F.b)[i + 1]'(by cases h : F.b with grind)} := by
  simpa using (F.isTriangle_bDual_joints (!F.b) i (by cases h : F.b with grind))

lemma isTriangle_joint (F : M.Fan) (i : ℕ) {hi : i + 1 < (F.joints false).length} :
    (M.IsTriangle {(F.joints false)[i], (F.joints true)[i + F.b.toNat]'
      (by simpa using F.lt_length_joints_of_lt_length_joints_add_one true hi),
      (F.joints false)[i + 1]}) := by
  simpa using F.isTriangle_bDual_joints false i hi

@[simp]
lemma cons_joints_self (F : M.Fan) (he : e ∉ F) (hT) :
    (F.cons he hT).joints F.b = F.joints F.b := by
  exact List.ext_getElem (by simp [length_joints]) fun i hi hi' ↦ by simp [joints_getElem]

@[simp]
lemma cons_joints_not (F : M.Fan) (he : e ∉ F) (hT) :
    (F.cons he hT).joints (!F.b) = e :: F.joints !F.b := by
  refine List.ext_getElem ?_ fun i hi hi' ↦ ?_
  · cases h : F.length.bodd with simp [length_joints, h]
  cases i with simp [joints_getElem, mul_add]

lemma cons_joints (F : M.Fan) (he : e ∉ F) (hT) (d : Bool) :
    (F.cons he hT).joints d = bif d == F.b then F.joints d else e :: F.joints d := by
  obtain rfl | rfl := d.eq_or_eq_not F.b <;> simp

@[simp]
lemma concat_joints_self (F : M.Fan) (he : e ∉ F) (hT) :
    (F.concat he hT).joints F.c = F.joints F.c := by
  refine List.ext_getElem ?_ fun i h₁ h₂ ↦ ?_
  · cases hbc : F.b == F.c with simp [length_joints, F.length_bodd, hbc]
  simp only [joints_getElem, concat_left]
  rw [concat_getElem_of_lt _]

@[simp]
lemma concat_joints_not (F : M.Fan) (he : e ∉ F) (hT) :
    (F.concat he hT).joints (!F.c) = F.joints (!F.c) ++ [e] := by
  refine List.ext_getElem ?_ fun i h₁ h₂ ↦ ?_
  · cases h : F.length.bodd with simp [length_joints, h]
  obtain rfl | hlt := (show i ≤ (F.joints !F.c).length by grind).eq_or_lt
  · simp only [joints_getElem, concat_left, bne_not, left_bne_right, Bool.not_not, Std.le_refl,
      getElem_append_right, tsub_self, List.getElem_cons_zero]
    convert F.concat_getElem_length
    cases h : F.length.bodd
    · simp [length_joints, h, F.length.two_mul_div2 h]
    simp [length_joints, h, F.length.two_mul_div2_add_one h]
  rw [joints_getElem, concat_getElem_of_lt _ (by grind), getElem_append_left hlt, joints_getElem]
  simp

@[simp]
lemma concat_joints (F : M.Fan) (he : e ∉ F) (hT) :
    (F.concat he hT).joints d = bif d == F.c then F.joints d else F.joints d ++ [e] := by
  obtain rfl | rfl := d.eq_or_eq_not F.c <;>
  simp

@[simp]
lemma ofPair_joints_self (he : ∀ d, (M.bDual d).IsNonloop e) (hf : ∀ d, (M.bDual d).IsNonloop f)
    (hef : e ≠ f) (b) : (ofPair he hf hef b).joints b = [e] := by
  simp [joints, getElem_ofPair]

@[simp]
lemma ofPair_joints_not (he : ∀ d, (M.bDual d).IsNonloop e) (hf : ∀ d, (M.bDual d).IsNonloop f)
    (hef : e ≠ f) (b) : (ofPair he hf hef b).joints (!b) = [f] := by
  simp [joints, getElem_ofPair]

@[simp]
lemma contract_joints (F : M.Fan) (C : Set α) {h₁ h₂ h₃ h₄ d} :
    (F.contract C h₁ h₂ h₃ h₄).joints d = F.joints d :=
  joints_congr _ _ rfl <| by simp

@[simp]
lemma delete_joints (F : M.Fan) (D : Set α) {h₁ h₂ h₃ h₄ d} :
    (F.delete D h₁ h₂ h₃ h₄).joints d = F.joints d :=
  joints_congr _ _ (by simp) <| by simp

@[simp]
lemma restrict_joints (F : M.Fan) (R : Set α) {h₁ h₂ h₃ h₄ d} :
    (F.restrict R h₁ h₂ h₃ h₄).joints d = F.joints d :=
  joints_congr _ _ (by simp) <| by simp

@[simp]
lemma contractHead_joints (F : M.Fan) {h₁ h₂ h₃ h₄ h₅ d} :
    (F.contractHead h₁ h₂ h₃ h₄ h₅).joints d = (F.tail h₁).joints d := rfl

lemma ofPair_joints (he : ∀ d, (M.bDual d).IsNonloop e) (hf : ∀ d, (M.bDual d).IsNonloop f)
    (hef : e ≠ f) (b) :
    (ofPair he hf hef b).joints d = bif d == b then [e] else [f] := by
  obtain rfl | rfl := d.eq_or_eq_not b <;>
  simp [joints, getElem_ofPair]

@[simp]
lemma reverse_joints (F : M.Fan) (d : Bool) : F.reverse.joints d = (F.joints d).reverse := by
  induction F using Fan.induction with
  | pair e f b he hf hef =>
    obtain rfl | rfl := d.eq_or_eq_not b <;>
    simp [ofPair_joints]
  | cons F₀ e heF₀ hT ih =>
    rw [cons_reverse, concat_joints, ih, cons_joints, Bool.apply_cond (f := List.reverse),
      reverse_right, reverse_cons]

@[simp]
lemma tail_joints_eq_tail (F : M.Fan) {hF : 3 ≤ F.length} :
    (F.tail hF).joints F.b = (F.joints F.b).tail := by
  induction F using Fan.induction with
  | pair => simp at hF
  | cons => rw [cons_tail_eq, cons_joints, cond_neg (by simp), tail_cons]

@[simp]
lemma tail_joints_eq_self (F : M.Fan) {hF : 3 ≤ F.length} :
    (F.tail hF).joints (!F.b) = F.joints (!F.b) := by
  induction F using Fan.induction with
  | pair => simp at hF
  | cons => rw [cons_tail_eq, cons_joints, cond_pos (by simp)]

lemma tail_joints (F : M.Fan) {hF : 3 ≤ F.length} :
    (F.tail hF).joints d = bif d == F.b then (F.joints d).tail else F.joints d := by
  obtain rfl | rfl := d.eq_or_eq_not F.b
  <;> simp

@[simp]
lemma dropLast_joints_eq_dropLast (F : M.Fan) {hF : 3 ≤ F.length} :
    (F.dropLast hF).joints F.c = (F.joints F.c).dropLast := by
  rw [dropLast, reverse_joints, ← reverse_left, tail_joints_eq_tail, reverse_joints,
    List.tail_reverse, List.reverse_reverse]

@[simp]
lemma dropLast_joints_eq_self (F : M.Fan) {hF : 3 ≤ F.length} :
    (F.dropLast hF).joints (!F.c) = F.joints (!F.c) := by
  rw [dropLast, reverse_joints, ← reverse_left, tail_joints_eq_self, reverse_joints,
    List.reverse_reverse]

@[simp]
lemma dropLast_joints (F : M.Fan) {hF : 3 ≤ F.length} :
    (F.dropLast hF).joints d = bif d == F.c then (F.joints d).dropLast else F.joints d := by
  obtain rfl | rfl := d.eq_or_eq_not F.c <;>
  simp

lemma joints_sublist (F : M.Fan) {d : Bool} : F.joints d <+ F := by
  induction F using Fan.induction with
  | pair e f F.b he hf hef => cases h : d == F.b with | _ => simp [ofPair_joints, h]
  | cons F₀ e heF₀ hT ih =>
    obtain rfl | rfl := d.eq_or_eq_not F₀.b
    · grw [cons_joints_self, ih, cons_toList, ← sublist_cons_self]
    grw [cons_joints_not, cons_toList, Sublist.cons_cons e ih]


@[simp]
lemma joints_bDual (F : M.Fan) (d d' : Bool) :
    (F.bDual d).joints d' = F.joints (d != d') :=
  joints_congr _ _ (by simp) <| by cases d with grind [bDual_left]

@[simp]
lemma joints_nodup (F : M.Fan) : (F.joints d).Nodup :=
  F.nodup.sublist F.joints_sublist

@[grind! .]
lemma length_joints_pos (F : M.Fan) : (F.joints d).length > 0 := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le F.length_ge_two
  simp [length_joints, hn, add_assoc, Nat.add_div2]

@[simp]
lemma joints_ne_nil (F : M.Fan) : F.joints d ≠ [] := by
  grind

lemma joints_getElem_zero (F : M.Fan) : (F.joints d)[0] = bif d == F.b then F[0] else F[1] := by
  obtain rfl | rfl := d.eq_or_eq_not F.b
  <;> simp [joints_getElem]

lemma joints_getLast (F : M.Fan) :
    (F.joints d).getLast (by simp) = bif d == F.c then F.getLast else F.getPenult := by
  rw [← reverse_getElem_one, ← reverse_getElem_zero, ← reverse_left,
    ← F.reverse.joints_getElem_zero]
  simp_rw [reverse_joints, getElem_zero_eq_head, head_reverse]

lemma joints_disjoint (F : M.Fan) (d : Bool) : Disjoint (F.joints d) (F.joints !d) := by
  induction F using Fan.induction with
  | pair e f F.b he hf hef =>
    obtain rfl | rfl := d.eq_or_eq_not F.b <;>
    simp [ofPair_joints, hef.symm, hef]
  | cons F₀ e heF₀ hT ih =>
    have aux {d' : Bool} : e ∉ F₀.joints d' := fun h ↦ heF₀ <| Sublist.mem h F₀.joints_sublist
    obtain rfl | rfl := d.eq_or_eq_not F₀.b <;>
    simpa [cons_joints, aux] using ih

/-- An interval consisting of a pair of joints, and the cojoints between them.
These are circuits in a fan. -/
def intervalC (F : M.Fan) (p q : ℕ) (d : Bool) (hpq : p < q) (hq : q < F.length)
    (_ : p.bodd = (F.b != d)) (_ : q.bodd = (F.b != d)) : List α :=
    (F[p] :: (((F : List α).zipIdx.extract p q).filter
      (fun x : α × ℕ ↦ x.2.bodd == (F.b == d))).map Prod.fst).concat F[q]

lemma getElem_mem_intervalC_iff (F : M.Fan) {p q d hpq hq hpb hqb hi} :
    F[i]'hi ∈ F.intervalC p q d hpq hq hpb hqb ↔
        i = p ∨ i = q ∨ (i.bodd = (F.b == d) ∧ p < i ∧ i < q) := by
  obtain rfl | hip := eq_or_ne i p
  · simp [intervalC]
  obtain rfl | hiq := eq_or_ne i q
  · simp [intervalC]
  simp [intervalC, -extract_eq_take_drop, mem_extract_iff_getElem, hip, hiq, hi,
    and_comm (a := (p ≤ i ∧ i < q)), show p < i ↔ p ≤ i by lia]

lemma getElem_mem_intervalC_iff_of_odd (F : M.Fan) {p q d hpq hq hpb hqb hi}
    (hib : i.bodd = (F.b == d)) :
    F[i]'hi ∈ F.intervalC p q d hpq hq hpb hqb ↔ p < i ∧ i < q := by
  obtain rfl | hip := eq_or_ne i p
  · cases d with simp [hib] at hpb
  obtain rfl | hiq := eq_or_ne i q
  · cases d with simp [hib] at hqb
  simp [getElem_mem_intervalC_iff, hib, hip, hiq]

lemma getElem_mem_intervalC_iff_of_even (F : M.Fan) {p q d hpq hq hpb hqb hi}
    (hib : i.bodd = (F.b != d)) :
    F[i]'hi ∈ F.intervalC p q d hpq hq hpb hqb ↔ i = p ∨ i = q := by
  cases d with simp [getElem_mem_intervalC_iff, hib]

lemma intervalC_add_two (F : M.Fan) (p q : ℕ) (d : Bool) (hpq : p < q) (hqF : q + 2 < F.length)
    (hp : p.bodd = (F.b != d)) (hq : (q + 2).bodd = (F.b != d)) :
    F.intervalC p (q + 2) d (by lia) hqF hp hq =
    (F.intervalC p q d hpq (by lia) hp (by simpa using hq)).dropLast ++ [F[q + 1], F[q + 2]] := by
  simp only [Nat.bodd_succ, Bool.not_not] at hq
  simp [intervalC, -extract_eq_take_drop]
  rw [← List.cons_append, ← List.cons_append, List.dropLast_concat, extract_add_one_right
    _ (by lia) (by simp [show q + 1 < F.length by lia]), append_cons (b := F[q + 1]),
    extract_add_one_right _ hpq.le (by simp [show q < F.length by lia])]
  simp only [extract_eq_take_drop, getElem_zipIdx, getElem_toList', zero_add, append_assoc,
    cons_append, nil_append, filter_append, map_append, cons.injEq, append_cancel_left_eq,
    _root_.true_and]
  rw [filter_cons_of_neg (by simp [hq, ← Bool.not_eq]), filter_cons_of_pos (by simp [hq]),
    filter_nil]
  rfl

lemma intervalC_add_two_self (F : M.Fan) (p : ℕ) (d : Bool) (hpF : p + 2 < F.length)
    (hp : p.bodd = (F.b != d)) :
    F.intervalC p (p + 2) d (by lia) hpF hp (by simpa) = [F[p], F[p + 1], F[p + 2]] := by

lemma intervalC_add_two_self (F : M.Fan) (p : ℕ) (d : Bool) (hpF : p + 2 < F.length)
    (hp : p.bodd = (F.b != d)) :
    F.intervalC p (p + 2) d (by lia) hpF hp (by simpa) = [F[p], F[p + 1], F[p + 2]] := by
  simp [intervalC]
