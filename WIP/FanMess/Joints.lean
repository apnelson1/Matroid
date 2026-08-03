import Matroid.Connectivity.FanWIP.Basic

set_option linter.style.longLine false

open Set List Bool


namespace Matroid.Fan

variable {α : Type*} {M : Matroid α} {X Y C K T : Set α} {e f g x y : α} {b b' c c' d : Bool}
    {n i j : ℕ} {J : List α} {F : M.Fan b c}

private lemma lt_aux (F : M.Fan b c) (d : Bool) (i : ℕ)
    (hi : i < (F.length + (b == d).toNat).div2) : 2 * i + (b != d).toNat < F.length := by
  rw [lt_div2_iff, Nat.lt_iff_add_one_le] at hi
  cases h : (b == d) with grind

/-- `F.joints d` is the sublist of elements of `F` that are in two `(M.bDual b)`-triangles of `F`.
We have `F[0] ∈ F.joints d` if and only if `d = b`, and otherwise `F[1] ∈ F.joints d`.  -/
def joints {b c} (F : M.Fan b c) (d : Bool) : List α := List.pmap
    (l := List.range (F.length + (b == d).toNat).div2)
    (P := fun (i : ℕ) ↦ i < (F.length + (b == d).toNat).div2)
    (f := fun i hi ↦ F[2 * i + (b != d).toNat]'(F.lt_aux d i (by simpa))) (by simp)

@[simp]
lemma joints_copy (F : M.Fan b c) {M' : Matroid α} {b' c' : Bool} {hM hb hc} :
    (F.copy M' b' c' hM hb hc).joints = F.joints := by
  subst hb hc hM
  exact funext fun _ ↦ rfl

lemma joints_getElem (F : M.Fan b c) (d : Bool) (i : ℕ) {hi : i < (F.joints d).length} :
    (F.joints d)[i] = F[2 * i + (b != d).toNat]'(F.lt_aux d i <| by simpa [joints] using hi) := by
  simp [joints]

lemma length_joints (F : M.Fan b c) (d : Bool) :
    (F.joints d).length = (F.length + (b == d).toNat).div2 := by
  simp [joints]

lemma joints_subset (F : M.Fan b c) {d : Bool} : {e | e ∈ F.joints d} ⊆ F := by
  intro e he
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  simp [joints_getElem]

lemma joints_subset_ground (F : M.Fan b c) {d : Bool} : {e | e ∈ F.joints d} ⊆ M.E := by
  grw [joints_subset, F.subset_ground]

@[grind! .]
lemma two_mul_length_joints_of_even (F : M.Fan b !b) (d : Bool) :
    2 * (F.joints d).length = F.length := by
  nth_rw 1 [length_joints, ← F.length.bodd_add_div2, add_comm (Bool.toNat _),
    add_assoc, Nat.two_mul_add_div2, Nat.add_div2, toNat_div2, zero_add, toNat_div2, zero_add,
    Bool.toNat_bodd, Bool.toNat_bodd, F.length_bodd_eq_false, Bool.false_and, mul_add,
    show 2 * false.toNat = F.length.bodd.toNat by grind, add_comm, Nat.bodd_add_div2]

@[grind! .]
lemma two_mul_length_joints_of_odd (F : M.Fan b b) :
    2 * (F.joints b).length = F.length + 1 := by
  suffices 2 * (F.length.div2 + 1) = F.length + 1 by simpa [F.length_joints, F.length_bodd_eq_true]
  nth_rw 1 [eq_comm, ← F.length.bodd_add_div2, F.length_bodd_eq_true, Bool.toNat_true]
  lia

@[grind! .]
lemma two_mul_length_joints_add_one_of_odd (F : M.Fan b b) :
    2 * (F.joints !b).length + 1 = F.length := by
  suffices 2 * F.length.div2 + 1 = F.length by simpa [F.length_joints]
  nth_rw 1 [eq_comm, ← F.length.bodd_add_div2, F.length_bodd_eq_true, Bool.toNat_true, add_comm]

/-- In an even fan, there is the same number of both types of `joints`. -/
@[grind! .]
lemma length_joints_eq_length_joints (F : M.Fan b !b) (d d' : Bool) :
    (F.joints d).length = (F.joints d').length := by
  rw [← Nat.mul_right_inj (a := 2) (by simp), two_mul_length_joints_of_even,
    two_mul_length_joints_of_even]

lemma getElem_mem_joints_iff {hi : i < F.length} : F[i] ∈ F.joints d ↔ i.bodd = (b != d) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨j, hj, hij⟩ := List.getElem_of_mem h
    obtain rfl : 2 * j + (b != d).toNat = i := by simpa [joints_getElem] using hij
    simp
  have hi_eq := h ▸ i.bodd_add_div2
  have := F.joints_getElem d i.div2 (hi := by grind [length_joints])
  simp_rw [add_comm, hi_eq] at this
  rw [← this]
  exact List.getElem_mem _

@[grind! .]
lemma length_joints_left_ge (F : M.Fan b c) : F.length ≤ 2 * (F.joints b).length := by
  obtain rfl | rfl := c.eq_or_eq_not b <;> grind

@[grind! .]
lemma length_joints_not_left_le (F : M.Fan b c) : 2 * (F.joints !b).length ≤ F.length := by
  obtain rfl | rfl := c.eq_or_eq_not b <;> grind

@[grind! .]
lemma length_joints_right_ge (F : M.Fan b c) : F.length ≤ 2 * (F.joints c).length := by
  obtain rfl | rfl := c.eq_or_eq_not b <;> grind

@[grind! .]
lemma length_joints_not_right_le (F : M.Fan b c) : 2 * (F.joints !c).length ≤ F.length := by
  obtain rfl | rfl := c.eq_or_eq_not b <;> grind

@[grind! .]
lemma length_joints_le_length_joints_add_one (F : M.Fan b c) (d d' : Bool) :
    (F.joints d).length ≤ (F.joints d').length + 1 := by
  obtain rfl | rfl := c.eq_or_eq_not b
  · obtain rfl | rfl := d'.eq_or_eq_not d
    · simp
    rw [← Nat.mul_le_mul_left_iff (show 0 < 2 by lia)]
    obtain rfl | rfl := d.eq_or_eq_not c <;> grind
  grind

@[grind =>]
lemma lt_length_joints_of_lt_length_joints_add_one (F : M.Fan b c) (d' : Bool)
    (hi : i + 1 < (F.joints d).length) : i + (b != d).toNat < (F.joints d').length := by
  -- grw [← Nat.add_one_lt_add_one_iff, ← F.length_joints_le_length_joints_add_one d]
  obtain rfl | rfl := d.eq_or_eq_not d'
  · grind
  obtain rfl | rfl := c.eq_or_eq_not b
  · rw [← Nat.mul_lt_mul_left (show 0 < 2 by simp)] at ⊢ hi
    obtain rfl | rfl := d'.eq_or_eq_not c <;> grind
  grind

/-- Any joint is in a triangle with the next cojoint and the joint after that. -/
lemma isTriangle_bDual_joints (F : M.Fan b c) (d : Bool) (i : ℕ)
    (hi : i + 1 < (F.joints d).length) :
    ((M.bDual d).IsTriangle {(F.joints d)[i], (F.joints (!d))[i + (b != d).toNat]'
      (F.lt_length_joints_of_lt_length_joints_add_one (!d) hi), (F.joints d)[i + 1]}) := by
  simp only [joints_getElem]
  generalize_proofs h1 h2
  convert F.isTriangle (i := 2 * i + (b != d).toNat) (by lia) using 4
  · simp
  · rw [show (b != !d) = !(b != d) by simp]
    have hwin := (b != d).toNat_add_toNat_bnot
    lia
  grind

/-- Any joint is in a triad with the cojoints before and after it. This is the version where
the fan starts with a cojoint. -/
lemma isTriangle_bDual_cojoints (F : M.Fan b c) (i : ℕ)
    (hi : i + (b != c).toNat < (F.joints (!b)).length) :
    (M.bDual b).IsTriangle {(F.joints b)[i], (F.joints !b)[i], (F.joints b)[i + 1]} := by
  simpa using (F.isTriangle_bDual_joints b i (by grind))

/-- Any joint is in a triad with the cojoints before and after it. This is the version where
the fan starts with a joint. -/
lemma isTriangle_bDual_cojoints' {b c} (F : M.Fan b c) (i : ℕ)
    (hi : i + 1 + (b == c).toNat < (F.joints b).length) :
    (M.bDual (!b)).IsTriangle {(F.joints !b)[i]'(by cases b with grind),
      (F.joints b)[i + 1], (F.joints !b)[i + 1]'(by cases b with grind)} := by
  simpa using (F.isTriangle_bDual_joints (!b) i (by cases b with grind))

lemma isTriangle_joint (F : M.Fan b c) (i : ℕ) {hi : i + 1 < (F.joints false).length} :
    (M.IsTriangle {(F.joints false)[i], (F.joints true)[i + b.toNat]'
      (by simpa using F.lt_length_joints_of_lt_length_joints_add_one true hi),
      (F.joints false)[i + 1]}) := by
  simpa using F.isTriangle_bDual_joints false i hi

@[simp]
lemma cons_joints_self (F : M.Fan b c) {b'} (hb : b' = !b) (he : e ∉ F)
    (hT : (M.bDual (!b)).IsTriangle {e, F[0], F[1]}) :
    (F.cons he hT b' hb).joints b = F.joints b := by
  subst hb
  exact List.ext_getElem (by simp [length_joints]) fun i hi hi' ↦ by simp [joints_getElem]

@[simp]
lemma cons_joints_not (F : M.Fan b c) {b'} (hb : b' = !b) (he : e ∉ F)
    (hT : (M.bDual !b).IsTriangle {e, F[0], F[1]}) :
    (F.cons he hT b' hb).joints (!b) = e :: F.joints !b := by
  subst hb
  refine List.ext_getElem ?_ fun i hi hi' ↦ ?_
  · cases h : F.length.bodd with simp [length_joints, h]
  cases i with simp [joints_getElem, mul_add]

lemma cons_joints (F : M.Fan b c) (he : e ∉ F) (hT : (M.bDual !b).IsTriangle {e, F[0], F[1]})
    {b'} (hb : b' = !b) (d : Bool) :
    (F.cons he hT b' hb).joints d = bif d == b then F.joints d else e :: F.joints d := by
  subst hb
  obtain rfl | rfl := d.eq_or_eq_not b <;> simp

@[simp]
lemma concat_joints_self (F : M.Fan b c) (he : e ∉ F)
    (hT : (M.bDual !c).IsTriangle {F.getPenult, F.getLast, e}) {c'} (hc : c' = !c) :
    (F.concat he hT c' hc).joints c = F.joints c := by
  refine List.ext_getElem ?_ fun i h₁ h₂ ↦ ?_
  · cases hbc : b == c with simp [length_joints, F.length_bodd, hbc]
  obtain rfl | rfl := b.eq_or_eq_not c
  · simp only [joints_getElem, bne_self_eq_false, Bool.toNat_false, add_zero]
    rw [concat_getElem_of_lt]
  simp only [joints_getElem, Bool.not_bne, bne_self_eq_false, Bool.not_false, Bool.toNat_true]
  rw [concat_getElem_of_lt]

@[simp]
lemma concat_joints_not (F : M.Fan b c) (he : e ∉ F)
    (hT : (M.bDual !c).IsTriangle {F.getPenult, F.getLast, e}) :
    (F.concat he hT).joints (!c) = F.joints (!c) ++ [e] := by
  refine List.ext_getElem ?_ fun i h₁ h₂ ↦ ?_
  · obtain rfl | rfl := b.eq_or_eq_not c
    <;> simp [length_joints, F.length_bodd]
  obtain rfl | hlt := (show i ≤ (F.joints !c).length by grind).eq_or_lt
  · simp only [joints_getElem, Bool.bne_not, Bool.bnot_bne, Std.le_refl, getElem_append_right,
      tsub_self, List.getElem_cons_zero]
    convert F.concatEq_getElem_length
    obtain rfl | rfl := b.eq_or_eq_not c <;>
    grind
  rw [joints_getElem, concat_getElem_of_lt, getElem_append_left hlt, joints_getElem]

@[simp]
lemma ofPair_joints_self (he : ∀ d, (M.bDual d).IsNonloop e) (hf : ∀ d, (M.bDual d).IsNonloop f)
    (hef : e ≠ f) (b) : (ofPair he hf hef b).joints b = [e] := by
  simp [joints, getElem_ofPair]

@[simp]
lemma ofPair_joints_not (he : ∀ d, (M.bDual d).IsNonloop e) (hf : ∀ d, (M.bDual d).IsNonloop f)
    (hef : e ≠ f) (b) : (ofPair he hf hef b).joints (!b) = [f] := by
  simp [joints, getElem_ofPair]

lemma ofPair_joints (he : ∀ d, (M.bDual d).IsNonloop e) (hf : ∀ d, (M.bDual d).IsNonloop f)
    (hef : e ≠ f) (b c) (hbc) :
    (ofPair he hf hef b c hbc).joints d = bif d == b then [e] else [f] := by
  subst hbc
  obtain rfl | rfl := d.eq_or_eq_not b
  · simp [joints, getElem_ofPair]
  simp [joints, getElem_ofPair]

@[simp]
lemma reverse_joints (F : M.Fan b c) (d : Bool) : F.reverse.joints d = (F.joints d).reverse := by
  induction F using Fan.induction with
  | pair e f b he hf hef =>
    obtain rfl | rfl := d.eq_or_eq_not b <;>
    simp [ofPair_joints]
  | cons b c F₀ e heF₀ hT ih =>
    obtain rfl | rfl := d.eq_or_eq_not b
    · rw [cons_reverse, concat_joints_self, cons_joints_self, ih]
    rw [cons_reverse, concat_joints_not, cons_joints_not, reverse_cons, append_cancel_right_eq, ih]

lemma tail_joints (F : M.Fan b c) {hF : 3 ≤ F.length} {b'} {hb : b' = !b} :
    (F.tail hF b' hb).joints b = (F.joints b).tail := by
  induction F using Fan.induction with
  | pair => simp at hF
  | cons => rw [cons_tail_eq_copy, joints_copy, cons_joints, cond_neg (by simp), tail_cons]

lemma tail_joints_eq_self (F : M.Fan b c) {hF : 3 ≤ F.length} {b'} {hb : b' = !b} :
    (F.tail hF b' hb).joints b' = F.joints b' := by
  induction F using Fan.induction with
  | pair => simp at hF
  | cons => rw [cons_tail_eq_copy, joints_copy, cons_joints, cond_pos (by simp [hb])]

lemma dropLast_joints (F : M.Fan b c) {hF : 3 ≤ F.length} {c'} {hc : c' = !c} :
    (F.dropLast hF c' hc).joints c = (F.joints c).dropLast := by
  rw [dropLast, reverse_joints, tail_joints, reverse_joints, List.tail_reverse,
    List.reverse_reverse]

lemma dropLast_joints_eq_self (F : M.Fan b c) {hF : 3 ≤ F.length} {c' hc'} :
    (F.dropLast hF c' hc').joints c' = F.joints c' := by
  rw [dropLast, reverse_joints, tail_joints_eq_self, reverse_joints, List.reverse_reverse]

lemma joints_sublist (F : M.Fan b c) {d : Bool} : F.joints d <+ F := by
  induction F using Fan.induction with
  | pair e f b he hf hef => cases h : d == b with | _ => simp [ofPair_joints, h]
  | cons b c F₀ e heF₀ hT ih =>
    obtain rfl | rfl := d.eq_or_eq_not b
    · grw [cons_joints_self, ih, cons_toList, ← sublist_cons_self]
    grw [cons_joints_not, cons_toList, Sublist.cons_cons e ih]

lemma joints_bDual (F : M.Fan b c) (d d' : Bool) :
    (F.bDual d).joints d' = F.joints (d != d') := by
  cases d
  cases d'
  ·
    -- rw [joints, joints]
    -- simp_rw [joints]
    rfl
  simp only [joints, bDual_getElem, bDual_length, show (((b != d) == d') = (b == (d != d'))) from sorry,
    show (((b != d) != d') = (b != (d != d'))) from sorry]

  convert rfl using 2
  rfl
  convert rfl using 6


@[simp]
lemma joints_nodup (F : M.Fan b c) : (F.joints d).Nodup :=
  F.nodup.sublist F.joints_sublist

@[grind! .]
lemma length_joints_pos (F : M.Fan b c) : (F.joints d).length > 0 := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le F.length_ge_two
  simp [length_joints, hn, add_assoc, Nat.add_div2]

@[simp]
lemma joints_ne_nil (F : M.Fan b c) : F.joints d ≠ [] := by
  grind

lemma joints_getElem_zero (F : M.Fan b c) : (F.joints d)[0] = bif d == b then F[0] else F[1] := by
  obtain rfl | rfl := d.eq_or_eq_not b
  <;> simp [joints_getElem]

lemma joints_getLast (F : M.Fan b c) :
    (F.joints d).getLast (by simp) = bif d == c then F.getLast else F.getPenult := by
  rw [← reverse_getElem_one, ← reverse_getElem_zero, ← F.reverse.joints_getElem_zero]
  simp_rw [reverse_joints, getElem_zero_eq_head, head_reverse]

lemma joints_disjoint (F : M.Fan b c) (d : Bool) : Disjoint (F.joints d) (F.joints !d) := by
  induction F using Fan.induction with
  | pair e f b he hf hef =>
    obtain rfl | rfl := d.eq_or_eq_not b <;>
    simp [ofPair_joints, hef.symm, hef]
  | cons b c F₀ e heF₀ hT ih =>
    have aux {d' : Bool} : e ∉ F₀.joints d' := fun h ↦ heF₀ <| Sublist.mem h F₀.joints_sublist
    obtain rfl | rfl := d.eq_or_eq_not b <;>
    simpa [cons_joints, aux] using ih
