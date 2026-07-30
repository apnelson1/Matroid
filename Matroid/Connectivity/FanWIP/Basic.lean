import Matroid.Connectivity.Separation.Tutte
import Matroid.ForMathlib.List.Set
import Matroid.ForMathlib.Parity

set_option linter.style.longLine false

open Set List


lemma Nat.lt_of_le_of_bodd_ne {a b : ℕ} (hab : a ≤ b) (hab' : a.bodd ≠ b.bodd) : a < b := by
  grind

lemma le_div2_iff {m n : ℕ} : m ≤ n.div2 ↔ 2 * m + n.bodd.toNat ≤ n := by
  have := n.bodd_add_div2
  lia

lemma lt_div2_iff {m n : ℕ} : m < n.div2 ↔ 2 * m + n.bodd.toNat + 1 < n := by
  have := n.bodd_add_div2
  lia

@[simp]
lemma Nat.two_mul_add_div2 (n m : ℕ) : (2 * n + m).div2 = n + m.div2 := by
  grind

@[simp]
lemma Nat.add_two_mul_div2 (n m : ℕ) : (n + 2 * m).div2 = n.div2 + m := by
  grind

@[simp]
lemma toNat_div2 (b : Bool) : b.toNat.div2 = 0 := by
  cases b with simp

lemma Nat.add_div2 (m n : ℕ) : (m + n).div2 = m.div2 + n.div2 + (m.bodd && n.bodd).toNat := by
  nth_rw 1 [← m.bodd_add_div2, add_right_comm, Nat.add_two_mul_div2,
    ← n.bodd_add_div2, ← add_assoc, Nat.add_two_mul_div2]
  cases h : m.bodd
  · simp [add_comm]
  cases h' : n.bodd
  · simp [add_comm]
  grind

namespace Matroid

-- variable {J : Bool → List α}

variable {α : Type*} {M : Matroid α} {X Y C K T : Set α} {e f g x y : α} {b c d : Bool}
    {J : Bool → List α} {L : List α} {n i j : ℕ} {J : List α} {b b' c : Bool} {L : List ℕ}

@[ext]
structure Fan (M : Matroid α) (b c : Bool) where
  toList : List α
  toList_nodup : toList.Nodup
  toList_length_ge : 2 ≤ toList.length
  toList_length_bodd : toList.length.bodd = (b == c)
  isNonloop' : ∀ i (hi : i < toList.length) (d : Bool), (M.bDual d).IsNonloop toList[i]
  isTriangle' : ∀ i (hi : i + 2 < toList.length), (M.bDual (b != i.bodd)).IsTriangle
    {toList[i], toList[i + 1], toList[i + 2]}

namespace Fan

instance coeList : CoeOut (M.Fan b c) (List α) where coe F := F.toList

def length (F : M.Fan b c) : ℕ := List.length (F : List α)

@[grind! .]
lemma length_bodd (F : M.Fan b c) : F.length.bodd = (b == c) :=
  F.toList_length_bodd

lemma length_bodd_eq_false (F : M.Fan b !b) : F.length.bodd = false := by
  grind

lemma length_bodd_eq_true (F : M.Fan b b) : F.length.bodd = true := by
  grind

@[grind! .]
lemma length_ge_two (F : M.Fan b c) : 2 ≤ F.length :=
  F.toList_length_ge

@[grind! .]
lemma length_ge_three (F : M.Fan b b) : 3 ≤ F.length :=
  F.length_ge_two.eq_or_lt.elim (fun h ↦ by simpa [F.length_bodd] using congr_arg Nat.bodd h) id

@[simp, grind=]
lemma length_toList (F : M.Fan b c) : F.toList.length = F.length := rfl

@[simp]
lemma toList_ne_nil (F : M.Fan b c) : (F : List α) ≠ [] := by
  grw [← length_pos_iff, length_toList, ← length_ge_two]
  simp

instance : GetElem (M.Fan b c) Nat α (fun t i => i < t.length) where
  getElem := fun t i h => t.toList[i]

instance : Membership α (M.Fan b c) where mem F e := e ∈ (F : List α)

@[simp]
lemma getElem_toList' (F : Fan M b c) (i : ℕ) {hi : i < F.length} : (F : List α)[i] = F[i] := rfl

@[simp]
lemma getElem_toList (F : Fan M b c) (i : ℕ) {hi : i < (F : List α).length} :
    (F : List α)[i] = F[i] := rfl


macro_rules
  | `(tactic| get_elem_tactic_extensible) =>
    `(tactic| grind[List.length_rotate, Nat.add_one_lt_of_bodd_eq])

@[simp]
lemma toList_head (F : M.Fan b c) : F.toList.head (by simp) = F[0] := by
  rw [← getElem_toList', ← getElem_zero_eq_head (by grind)]
  rfl

def toSet (F : Fan M b c) : Set α := {e | e ∈ F}

instance coeSet : CoeOut (M.Fan b c) (Set α) where coe F := F.toSet

attribute [coe] Fan.toList Fan.toSet

@[simp]
lemma mem_toSet (F : M.Fan b c) : e ∈ (F : Set α) ↔ e ∈ F := Iff.rfl

@[simp]
lemma mem_toList (F : M.Fan b c) : e ∈ (F : List α) ↔ e ∈ F := Iff.rfl

@[simp]
lemma ofPred_mem_toList_eq (F : M.Fan b c) : {e | e ∈ (F : List α)} = F := rfl

@[simp]
lemma ofPred_mem_eq (F : M.Fan b c) : {e | e ∈ F} = F := rfl

@[simp]
lemma getElem_mem_toSet (F : M.Fan b c) (hi : i < F.length) : F[i] ∈ (F : Set α) :=
  getElem_mem hi

@[simp]
protected lemma nodup (F : M.Fan b c) : (F : List α).Nodup :=
  F.toList_nodup

@[simp]
lemma encard_toSet_eq (F : M.Fan b c) : (F : Set α).encard = F.length := by
  rw [← ofPred_mem_toList_eq, F.nodup.encard_toSet_eq, length_toList]

lemma toSet_nontrivial (F : M.Fan b c) : (F : Set α).Nontrivial := by
  grw [← two_le_encard_iff_nontrivial, encard_toSet_eq, ← F.length_ge_two, ENat.coe_eq_ofNat]

lemma isNonloop (F : M.Fan b c) {hi : i < F.length} {d : Bool} : (M.bDual d).IsNonloop F[i] :=
  F.isNonloop' i hi d

lemma getElem_of_mem (F : M.Fan b c) (heF : e ∈ F) : ∃ (i : ℕ) (hi : i < F.length), F[i] = e :=
  List.getElem_of_mem heF

@[simp]
lemma isNonloop_of_mem {F : M.Fan b c} (heF : e ∈ F) (d : Bool) : (M.bDual d).IsNonloop e := by
  obtain ⟨i, hi, rfl⟩ := F.getElem_of_mem heF
  exact F.isNonloop

@[simp, grind →]
lemma getElem_inj (F : M.Fan b c) {i j} {hi : i < F.length} {hj : j < F.length} :
    F[i] = F[j] ↔ i = j :=
  F.nodup.getElem_inj_iff

lemma isTriangle (F : M.Fan b c) (i : ℕ) (hi : i + 2 < F.length) :
    (M.bDual (b != i.bodd)).IsTriangle {F[i], F[i + 1], F[i + 2]} :=
  F.isTriangle' i hi

lemma isTriangle_of_eq {F : M.Fan b c} (i : ℕ) (hi : i + 2 < F.length) (h_eq : i.bodd = b) :
    M.IsTriangle {F[i], F[i + 1], F[i + 2]} := by
  simpa [h_eq] using F.isTriangle i hi

lemma Bool.bnot_toNat (b : Bool) : (!b).toNat = 1 - b.toNat := by
  cases b with simp

-- lemma Nat.two_mul_div2 (n : ℕ) : 2 * n.div2 = n - n.bodd.toNat := by
--   refine Nat.eq_sub_of_add_eq ?_
--   rw [add_comm, n.bodd_add_div2]


@[simps]
def copy (F : M.Fan b c) (M' : Matroid α) (b' c' : Bool) (hM : M = M')
    (hb : b = b') (hc : c = c') : M'.Fan b' c' where
  toList := F
  toList_nodup := F.nodup
  toList_length_ge := F.toList_length_ge
  toList_length_bodd := hb ▸ hc ▸ F.toList_length_bodd
  isNonloop' := by subst hb hc hM; exact F.isNonloop'
  isTriangle' := by subst hb hc hM; exact F.isTriangle'

@[simp]
lemma copy_coeSet_eq (F : M.Fan b c) (M' : Matroid α) (b' c' : Bool) (hM : M = M')
    (hb : b = b') (hc : c = c') : (F.copy M' b' c' hM hb hc : Set α) = F := rfl

@[simp]
lemma copy_length (F : M.Fan b c) (M' : Matroid α) (b' c' : Bool) (hM : M = M')
    (hb : b = b') (hc : c = c') : (F.copy M' b' c' hM hb hc).length = F.length := rfl

@[simp]
lemma copy_getElem (F : M.Fan b c) (M' : Matroid α) (b' c' : Bool) (hM : M = M')
    (hb : b = b') (hc : c = c') (i : ℕ) {hi : i < (F.copy M' b' c' hM hb hc).length} :
    (F.copy M' b' c' hM hb hc)[i] = F[i] := rfl

@[simps]
protected def consEq (F : M.Fan b c) (hb : b' = !b) (heF : e ∉ F)
    (hT : (M.bDual b').IsTriangle {e, F[0], F[1]}) : M.Fan b' c where
  toList := e :: F
  toList_nodup := by simpa
  toList_length_ge := by grind
  toList_length_bodd := by
    simp [F.length_bodd, hb]
    cases b' with grind
  isNonloop' := by
    rintro (rfl | i) hi d
    · simpa [hb] using hT.isNonloop_bDual₁ (b := (b == d))
    simpa using F.isNonloop
  isTriangle' := by
    rintro (rfl | i) hi
    · simpa [← hb]
    simpa [hb] using! F.isTriangle i (by grind)

@[simp]
lemma cons_length (F : M.Fan b c) (hb : b' = !b) (heF : e ∉ F) (hT) :
    (F.consEq hb heF hT).length = F.length + 1 := by
  rw [← length_toList, consEq_toList]
  simp

@[simp]
lemma cons_toSet (F : M.Fan b c) (hb : b' = !b) (heF : e ∉ F) (hT) :
    (F.consEq hb heF hT : Set α) = insert e (F : Set α) := by
  rw [← ofPred_mem_toList_eq]
  simp [mem_cons, mem_toList, ofPred_or]

@[simp]
lemma getElem_cons_zero (F : M.Fan b c) (hb : b' = !b) (heF : e ∉ F) (hT) :
    (F.consEq hb heF hT)[0] = e := rfl

@[simp]
lemma getElem_cons_succ (F : M.Fan b c) (hb : b' = !b) (heF : e ∉ F) (hT)
    (hi : i + 1 < (F.consEq hb heF hT).length) :
    (F.consEq hb heF hT)[i + 1] = F[i]'(by simpa using hi) := rfl

@[simps!, reducible]
protected def cons (F : M.Fan b c) (heF : e ∉ F) (hT : (M.bDual (!b)).IsTriangle {e, F[0], F[1]}) :
    M.Fan (!b) c := F.consEq rfl heF hT

@[simps!, reducible]
protected def consNot (F : M.Fan (!b) c) (heF : e ∉ F)
  (hT : (M.bDual b).IsTriangle {e, F[0], F[1]}) : M.Fan b c :=
    F.consEq (by simp) heF hT

abbrev getLast (F : M.Fan b c) : α := F[F.length - 1]

abbrev getPenult (F : M.Fan b c) : α := F[F.length - 2]

lemma subset_ground (F : M.Fan b c) : (F : Set α) ⊆ M.E :=
  fun _ he ↦ (F.isNonloop_of_mem he false).mem_ground

@[simp]
lemma getElem_eq_getElem (F : M.Fan b c) (i : ℕ) (hi : i < (F : List α).length) :
    F[i] = F[i]'(show i < F.length from hi) :=
  rfl

@[simp]
lemma get_mem_ground (F : M.Fan b c) (i : ℕ) {hi : i < F.length} : F[i] ∈ M.E :=
  (F.isNonloop (d := false)).mem_ground

@[simp]
lemma mem_toList_getElems_iff (F : M.Fan b c) (i : ℕ) {hi : i < F.length} {s : Set ℕ} :
    F[i] ∈ (F : List α).getElems s ↔ i ∈ s :=
  F.nodup.getElem_mem_getElems_iff

@[simps]
def reverse (F : M.Fan b c) : M.Fan c b where
  toList := (F : List α).reverse
  toList_nodup := List.nodup_reverse.2 F.nodup
  toList_length_ge := by simp [F.length_ge_two]
  toList_length_bodd := by simp [F.length_bodd, eq_comm]
  isNonloop' i hi d := by
    simp only [getElem_reverse, length_toList, getElem_toList]
    exact F.isNonloop
  isTriangle' i hi := by
    simp only [getElem_reverse, length_toList, getElem_toList]
    simp only [length_reverse, length_toList] at hi
    convert (F.isTriangle (i := F.length - i - 3) (by lia)).reverse using 1
    · rw [Nat.sub_sub, Nat.bodd_sub (by lia), F.length_bodd, Nat.bodd_add]
      cases b with cases c with simp
    grind

@[simp]
lemma reverse_toSet (F : M.Fan b c) : (F.reverse : Set α) = F := by
  rw [← ofPred_mem_toList_eq]
  simp

@[simp]
lemma reverse_length (F : M.Fan b c) : F.reverse.length = F.length :=
  length_reverse ..

@[simp]
lemma mem_reverse (F : M.Fan b c) : e ∈ F.reverse ↔ e ∈ F :=
  List.mem_reverse

@[simp]
lemma reverse_getElem_zero (F : M.Fan b c) : F.reverse[0] = F.getLast := by
  simp_rw [getLast, ← getElem_toList', reverse_toList, List.getElem_reverse, tsub_zero]
  rfl

@[simp]
lemma reverse_getElem_one (F : M.Fan b c) : F.reverse[1] = F.getPenult := by
  simp_rw [getPenult, ← getElem_toList', reverse_toList, List.getElem_reverse, Nat.sub_sub,
    one_add_one_eq_two]
  rfl

def concatEq (F : M.Fan b c) (heF : e ∉ F) {c'} (hc' : c' = !c)
    (hT : (M.bDual c').IsTriangle {F.getPenult, F.getLast, e}) : M.Fan b c' :=
  ((F.reverse.consEq (b' := c') hc' (by simpa)) (by simpa using hT.reverse)).reverse

lemma concatEq_toList (F : M.Fan b c) (heF : e ∉ F) {c'} (hc' : c' = !c) (hT) :
    (F.concatEq heF hc' hT).toList = F.toList ++ [e] := by
  simp [concatEq]

@[simps!]
def bDual (F : M.Fan b c) (d : Bool) : (M.bDual d).Fan (b != d) (c != d) where
  toList := F
  toList_nodup := F.nodup
  toList_length_ge := F.length_ge_two
  toList_length_bodd := by simp [F.length_bodd]
  isNonloop' i hi d' := by simpa using F.isNonloop
  isTriangle' i hi := by cases d with simpa using! F.isTriangle i hi

@[reducible, simps!]
def ofbDual (F : (M.bDual d).Fan b c) : M.Fan (b != d) (c != d) :=
  (F.bDual d).copy _ _ _ (by simp) (by simp) (by simp)

@[simp]
lemma bDual_length (F : M.Fan b c) (d : Bool) : (F.bDual d).length = F.length := rfl

@[simp]
lemma bDual_toSet (F : M.Fan b c) (d : Bool) : (F.bDual d : Set α) = F := rfl

@[reducible]
def dual (F : M.Fan b c) : (M✶.Fan (!b) (!c)) :=
  (F.bDual true).copy _ _ _ rfl (by simp) (by simp)

@[reducible]
def ofDual (F : M✶.Fan b c) : (M.Fan (!b) (!c)) :=
  (F.bDual true).copy _ _ _ (by simp) (by simp) (by simp)

@[simps]
def ofPair (he : ∀ i, (M.bDual i).IsNonloop e) (hf : ∀ i, (M.bDual i).IsNonloop f) (hef : e ≠ f)
    (b : Bool) : M.Fan b !b where
  toList := [e, f]
  toList_nodup := by simpa
  toList_length_ge := by simp
  toList_length_bodd := by simp
  isNonloop' := by grind [Nat.le_one_iff_eq_zero_or_eq_one]
  isTriangle' := by simp

@[simp]
lemma ofPair_toSet (he : ∀ i, (M.bDual i).IsNonloop e) (hf : ∀ i, (M.bDual i).IsNonloop f)
    (hef : e ≠ f) (b : Bool) : (Fan.ofPair he hf hef b : Set α) = {e, f} := by
  rw [← ofPred_mem_toList_eq, ofPair_toList]
  simp [ofPred_or, pair_comm]

@[simp]
lemma ofPair_length (he : ∀ i, (M.bDual i).IsNonloop e) (hf : ∀ i, (M.bDual i).IsNonloop f)
    (hef : e ≠ f) (b : Bool) : (Fan.ofPair he hf hef b).length = 2 := rfl

@[simps]
def ofTriangle (hT : M.IsTriangle {e, f, g}) : M.Fan false false where
  toList := [e, f, g]
  toList_nodup := by simp [hT.ne₁₂, hT.ne₁₃, hT.ne₂₃]
  toList_length_ge := by simp
  toList_length_bodd := by simp
  isNonloop' i hi d := hT.isNonloop_bDual_of_mem <| by grind
  isTriangle' := by
    rintro (rfl | i) hi
    · simpa
    simp [add_assoc] at hi

@[simps!, reducible]
def ofTriangle_bDual (h : (M.bDual b).IsTriangle {e, f, g}) : M.Fan b b :=
  (ofTriangle h).ofbDual.copy _ _ _ rfl (by simp) (by simp)

lemma length_sub_one_bodd_eq (F : M.Fan b c) : (F.length - 1).bodd = (b != c) := by
  rw [Nat.bodd_sub (by grind)]
  simp [F.length_bodd]

lemma IsFan.mod_lt_length (F : M.Fan b c) (i : ℕ) : i % F.length < F.length :=
  Nat.mod_lt i (by grind)

lemma IsFan.bool_right_eq (F : M.Fan b c) : c = (b == F.length.bodd) := by
  simp [F.length_bodd]

lemma IsFan.bool_left_eq (F : M.Fan b c) : b = (c == F.length.bodd) := by
  cases b with simp [F.length_bodd]

@[simps]
def tail (F : M.Fan b c) (hF : 3 ≤ F.length) : M.Fan (!b) c where
  toList := (F : List α).tail
  toList_nodup := F.nodup.tail
  toList_length_ge := by grind
  toList_length_bodd := by
    simp only [length_tail, length_toList, F.length_sub_one_bodd_eq]
    cases b with cases c with simp
  isNonloop' i hi d := by simpa using! F.isNonloop (i := i + 1) (d := d)
  isTriangle' i hi := by simpa using! F.isTriangle (i := i + 1) (by grind)

def dropLast (F : M.Fan b c) (hF : 3 ≤ F.length) : M.Fan b (!c) :=
  (F.reverse.tail (by simpa)).reverse

lemma eq_tail_cons (F : M.Fan b c) (hF : 3 ≤ F.length) : F = (F.tail hF).consNot (e := F[0])
    (fun h0 ↦ by simpa using F.nodup.rel_head_tail (a := F[0]) h0)
    (by simp_rw [← getElem_toList']; simpa using! F.isTriangle 0 (by lia)) := by
  ext i e
  simp only [getElem?_eq_some_iff, getElem_toList, length_toList, getElem_toList', consEq_toList,
    tail_toList, length_cons, length_tail, Order.lt_add_one_iff]
  obtain rfl | i := i
  · simp [show 0 < F.length by lia]
  simp only [List.getElem_cons_succ, getElem_tail, getElem_toList, Order.add_one_le_iff,
    show ∀ j, j < F.length - 1 ↔ j + 1 < F.length by grind]
  rfl

def joints' (F : M.Fan b c) : List α := List.pmap
    (l := List.range (F.length + (!b).toNat).div2)
    (P := fun (i : ℕ) ↦ i < (F.length + (!b).toNat).div2)
    (f := fun i hi ↦ F[2 * i + b.toNat]'
    (by rw [lt_div2_iff, Nat.lt_iff_add_one_le] at hi; cases b with grind))
    (by simp)

def joints (F : M.Fan b c) (d : Bool) : List α := (F.bDual d).joints'

lemma length_joints (F : M.Fan b c) (d : Bool) :
    (F.joints d).length = (F.length + (b == d).toNat).div2 := by
  rw [joints, joints', length_pmap, List.length_range, bDual_length, Bool.bnot_bne]

lemma two_mul_length_joints_of_even (F : M.Fan b !b) (d : Bool) :
    2 * (F.joints d).length = F.length := by
  nth_rw 1 [length_joints, ← F.length.bodd_add_div2, add_comm (Bool.toNat _),
    add_assoc, Nat.two_mul_add_div2, Nat.add_div2, toNat_div2, zero_add, toNat_div2, zero_add,
    Bool.toNat_bodd, Bool.toNat_bodd, F.length_bodd_eq_false, Bool.false_and, mul_add,
    show 2 * false.toNat = F.length.bodd.toNat by grind, add_comm, Nat.bodd_add_div2]

-- #exit


-- -- lemma IsFan.drop {k} (h : M.IsFan F b c) (hk : k + 2 ≤ F.length) :
-- --     M.IsFan (F.drop k) (if Even k then b else !b) c := by
-- --   induction k with
-- --   | zero => simpa
-- --   | succ k ih =>
-- --     convert (ih (by grind)).tail (by grind) using 1
-- --     · simp
-- --     grind


-- -- lemma IsFan.take {k} (h : M.IsFan F b c) (hk : 2 ≤ k) (hkle : k ≤ F.length) :
-- --     M.IsFan (F.take k) b (if Odd k then b else !b) := by
-- --   convert (h.reverse.drop (k := F.length - k) (by grind)).reverse using 1
-- --   · grind [List.drop_reverse]
-- --   obtain ⟨d, h_eq⟩ := exists_add_of_le hkle
-- --   simp only [h_eq, add_tsub_cancel_left, h.right_eq, Nat.odd_add]
-- --   split_ifs <;> grind

-- lemma isFan_cons_iff (hF : 3 ≤ F.length) : M.IsFan (x :: F) b c ↔
--     ∃ e f F₀, F = e :: f :: F₀ ∧ (M.bDual b).IsTriangle {x, e, f} ∧ x ∉ F ∧ M.IsFan F (!b) c := by
--   refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
--   · cases h with
--     | of_pair => simp at hF
--     | cons_triangle e z y F b c h heF hT => exact ⟨z, y, F, rfl, hT, by grind, by simpa⟩
--   obtain ⟨e, f, F, rfl, hT, hxF, hF'⟩ := h
--   refine hF'.cons_not (by grind) hT

-- lemma IsFan.of_cons (hF : M.IsFan (x :: F) b c) (h : 2 ≤ F.length) : M.IsFan F (!b) c := by
--   cases hF with | of_pair => simp at h | cons_triangle => simpa

-- lemma IsFan.exists_cons (hF : M.IsFan F b c) (h : 3 ≤ F.length) :
--     ∃ e F₀, F = e :: F₀ ∧ M.IsFan F₀ (!b) c := by
--   cases hF with grind

-- lemma IsFan.isTriangle_getElem (h : M.IsFan F b c) (i) (hi : i + 2 < F.length) :
--     (M.bDual (b != i.bodd)).IsTriangle {F[i], F[i + 1], F[i + 2]} := by
--   induction h generalizing i with
--   | of_pair => grind
--   | cons_triangle e x y F b c h heF hT ih =>
--     obtain rfl | i := i
--     · simpa
--     specialize ih i (by simpa using hi)
--     simpa

-- lemma IsFan.isTriangle_getElem_of_eq (h : M.IsFan F b c) (i) (hi : i + 2 < F.length)
--     (hib : i.bodd = b) : M.IsTriangle {F[i], F[i + 1], F[i + 2]} := by
--   simpa [hib.symm] using h.isTriangle_getElem i hi

-- lemma IsFan.isTriad_getElem_of_eq (h : M.IsFan F b c) (i) (hi : i + 2 < F.length)
--     (hib : i.bodd = !b) : M.IsTriad {F[i], F[i + 1], F[i + 2]} := by
--   simpa [hib] using h.isTriangle_getElem i hi

-- lemma IsFan.isTriangle_image_get (h : M.IsFan F b c) (hF : F.length = n + 2) (i : Fin n) :
--     (M.bDual (b != (i : ℕ).bodd)).IsTriangle
--       <| (fun j ↦ F.get (Fin.cast hF.symm j)) ''
--         {i.castSucc.castSucc, i.succ.castSucc, i.succ.succ} := by
--   convert h.isTriangle_getElem i.1 (by grind)
--   simp [image_insert_eq]

-- lemma isFan_of_forall_triangle (hF : 3 ≤ F.length) (hnd : F.Nodup)
--     (hT : ∀ i (hi : i + 2 < F.length),
--     (M.bDual (b != i.bodd)).IsTriangle {F[i], F[i + 1], F[i + 2]}) :
--     M.IsFan F b (b == F.length.bodd) := by
--   match F with
--   | [] => simp at hF
--   | [_] => simp at hF
--   | [_, _] => simp at hF
--   | e :: f :: g :: F =>
--     induction F generalizing e f g b with
--     | nil => simpa using (hT 0 (by simp)).isFan_of_bDual
--     | cons a F ih =>
--       have hwin := (ih f g a (b := !b) (by simp) (by grind) ?_).cons_not (e := e) (by grind) ?_
--       · cases b with simpa using hwin
--       · refine fun i hi ↦ ?_
--         have := hT (i + 1) (by grind)
--         simp at this
--         simp
--         assumption
--       simpa using hT 0 (by simp)

-- lemma isFan_of_eq_of_forall_triangle (hF : 3 ≤ F.length) (hnd : F.Nodup)
--     (hbc : (b == c) = F.length.bodd) (hT : ∀ i (hi : i + 2 < F.length),
--       (M.bDual (b != i.bodd)).IsTriangle {F[i], F[i + 1], F[i + 2]}) : M.IsFan F b c := by
--   convert isFan_of_forall_triangle hF hnd (b := b) hT
--   cases b with cases c with grind

-- lemma isFan_iff_forall (hF : 3 ≤ F.length) :
--     M.IsFan F b c ↔ (b == c) = F.length.bodd ∧ F.Nodup ∧ ∀ i (hi : i + 2 < F.length),
--     (M.bDual (b != i.bodd)).IsTriangle {F[i], F[i + 1], F[i + 2]} := by
--   refine ⟨fun h ↦ ⟨h.length_bodd_eq.symm, h.nodup, h.isTriangle_getElem⟩, fun ⟨hbc, hnd, h⟩ ↦ ?_⟩
--   convert isFan_of_forall_triangle hF hnd h
--   cases b with cases c with grind

-- @[simp]
-- lemma isFan_three_iff : M.IsFan [e, f, g] b c ↔ b = c ∧ (M.bDual b).IsTriangle {e, f, g} := by
--   refine ⟨fun h ↦ ⟨by simpa using h.length_bodd_eq, h.isTriangle_bDual rfl.le⟩, fun h ↦ ?_⟩
--   rw [← h.1]
--   exact h.2.isFan_of_bDual

-- lemma isFan_four_iff : M.IsFan [x, e, f, g] b c ↔ c = !b ∧
--     (M.bDual (!b)).IsTriangle {e, f, g} ∧ (M.bDual b).IsTriangle {x, e, f} ∧ x ≠ g := by
--   refine ⟨fun h ↦ ⟨?_, ?_, ?_, ?_⟩, fun ⟨hcb, hT, hT', hxg⟩ ↦ ?_⟩
--   · cases b with simpa using h.length_bodd_eq
--   · simpa using h.isTriangle_getElem 1 (by simp)
--   · exact h.isTriangle_bDual (by simp)
--   · grind [h.nodup]
--   simpa [hcb] using hT.isFan.cons (by simpa using hxg) (by simpa)

-- lemma IsFan.swap_middle (h : M.IsFan F b c) (h4 : F.length = 4) :
--     M.IsFan [F[0], F[2], F[1], F[3]] b c := by
--   obtain ⟨p, q, r, s, rfl⟩ := length_eq_four.1 h4
--   simp only [isFan_four_iff, ne_eq, getElem_cons_zero, getElem_cons_succ] at *
--   exact ⟨h.1, h.2.1.swap_left, h.2.2.1.swap_right, h.2.2.2⟩

-- /-- Induct by stripping two layers off the front of a fan to get a fan of the same type. -/
-- @[elab_as_elim]
-- lemma IsFan.induction₂
--     {motive : (M : Matroid α) → (F : List α) → (b c : Bool) → M.IsFan F b c → Prop}
--     (of_pair : ∀ M e f (he : ∀ i, (M.bDual i).IsNonloop e) (hf : ∀ i, (M.bDual i).IsNonloop f)
--       (hef : e ≠ f) d, motive M [e, f] d (!d) (isFan_pair he hf hef))
--     (of_isTriangle : ∀ M e f g d (h : (M.bDual d).IsTriangle {e, f, g}),
--       motive M [e, f, g] d d h.isFan_of_bDual)
--     (cons_cons : ∀ M e f x y F c d (h : M.IsFan (x :: y :: F) c d)
--       (hT : (M.bDual (!c)).IsTriangle {f, x, y}) (hf : f ∉ F)
--       (hT' : (M.bDual c).IsTriangle {e, f, x}) (he : e ∉ F) (hey : e ≠ y),
--       motive M _ _ _ h → motive M _ c d ((h.cons hf hT).cons_not (by grind) hT'))
--     (h : M.IsFan F b c) : motive M F b c h := by
--   obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h.two_le_length
--   induction k using Nat.twoStepInduction generalizing F b with
--   | zero =>
--     obtain ⟨e, f, rfl⟩ := length_eq_two.1 <| (add_zero (M := ℕ) _ ▸ hk)
--     obtain rfl | rfl := c.eq_or_eq_not b
--     · simpa using h.length_bodd_eq
--     apply of_pair _ _ _ (h.isNonloop_bDual (by simp)) (h.isNonloop_bDual (by simp))
--       (by simpa using h.nodup)
--   | one =>
--     obtain ⟨e, f, g, rfl⟩ := length_eq_three.1 <| (add_zero (M := ℕ) _ ▸ hk)
--     convert of_isTriangle M e f g b <| h.isTriangle_bDual (by simp)
--     simp [h.right_eq, show Odd 3 by decide]
--   | more n ih _ =>
--     obtain ⟨e, F, rfl, h1⟩ := h.exists_cons (by grind)
--     obtain ⟨f, F, rfl, h2⟩ := h1.exists_cons (by grind)
--     obtain ⟨x, F, rfl⟩ := F.exists_cons_of_length_pos (by grind)
--     obtain ⟨y, F, rfl⟩ := F.exists_cons_of_length_pos (by grind)
--     have hnd := h.nodup
--     exact cons_cons M e f x y F _ _ (by simpa using h2) (h1.isTriangle_bDual (by grind)) (by grind)
--       (h.isTriangle_bDual (by grind)) (by grind) (by grind) <| ih (by simpa using h2) (by grind)

-- /-- An induction principle about fans of even length. -/
-- @[elab_as_elim]
-- lemma IsFan.induction₂_even
--    {motive : (M : Matroid α) → (F : List α) → (b : Bool) → M.IsFan F b (!b) → Prop}
--     (of_pair : ∀ M e f (he : ∀ i, (M.bDual i).IsNonloop e) (hf : ∀ i, (M.bDual i).IsNonloop f)
--       (hef : e ≠ f) d, motive M [e, f] d (isFan_pair he hf hef))
--     (cons_cons : ∀ M e f x y F b (h : M.IsFan (x :: y :: F) b !b)
--       (hT : (M.bDual (!b)).IsTriangle {f, x, y}) (hf : f ∉ F)
--       (hT' : (M.bDual b).IsTriangle {e, f, x}) (he : e ∉ F) (hey : e ≠ y),
--       motive M _ _ h → motive M _ b ((h.cons hf hT).cons_not (by grind) hT'))
--     (h : M.IsFan F b !b) : motive M F b h := by
--   generalize hbc : (!b) = c
--   have h' : M.IsFan F b c := by rwa [← hbc]
--   induction h' using IsFan.induction₂ with
--   | of_pair => apply of_pair <;> assumption
--   | of_isTriangle => simpa using h.length_bodd_eq
--   | cons_cons => grind

-- @[elab_as_elim]
-- lemma IsFan.induction₂_odd
--    {motive : (M : Matroid α) → (F : List α) → (b : Bool) → M.IsFan F b b → Prop}
--     (of_triangle : ∀ M e f g b (hT : (M.bDual b).IsTriangle {e, f, g}),
--       motive M [e, f, g] b hT.isFan_of_bDual)
--     (cons_cons : ∀ M e f x y F b (h : M.IsFan (x :: y :: F) b b)
--       (hT : (M.bDual (!b)).IsTriangle {f, x, y}) (hf : f ∉ F)
--       (hT' : (M.bDual b).IsTriangle {e, f, x}) (he : e ∉ F) (hey : e ≠ y),
--       motive M _ _ h → motive M _ b ((h.cons hf hT).cons_not (by grind) hT'))
--     (h : M.IsFan F b b) : motive M F b h := by
--   obtain ⟨c, hcb, h'⟩ : ∃ c, c = b ∧ M.IsFan F b c := ⟨b, rfl, h⟩
--   induction h' using IsFan.induction₂ with grind

-- lemma IsFan.eRk_le (h : M.IsFan F b c) (hlen : 3 ≤ F.length) :
--     2 * M.eRk {e | e ∈ F} ≤ F.length + 1 + b.toNat + c.toNat := by
--   induction h with
--   | of_pair => simp at hlen
--   | cons_triangle e x y F b c h heF hT ih =>
--     cases F with
--     | nil =>
--       cases b
--       · grw [eRk_le_encard, ofPred_three, hT.three_elements, h.bool_right_eq,
--           show (2 : ℕ∞) * 3 ≤ 3 + 1 + 1 + 1 from rfl.le]
--         simp
--       grw [ofPred_three, IsTriangle.eRk (by simpa using hT), h.bool_right_eq,
--         show (2 : ℕ∞) * 2 ≤ 3 + 1 from rfl.le]
--       simp
--     | cons p F =>
--       simp_rw [List.mem_cons (b := e), ofPred_or, ofPred_eq_eq_singleton, singleton_union]
--       cases b
--       · grw [eRk_insert_le_add_one, mul_add, ih (by grind)]
--         simp [h.bool_right_eq]
--         enat_to_nat! <;> lia
--       grw [← eRk_closure_eq, closure_insert_eq_of_mem_closure, eRk_closure_eq, ih (by grind)]
--       · simp [h.bool_right_eq]
--       exact mem_of_mem_of_subset hT.mem_closure₁ <| M.closure_subset_closure <| by grind

-- lemma IsFiniteRankUniform.exists_isFan (h : M.IsFiniteUniform 2 2) (b : Bool) :
--     ∃ F, M.IsFan F b (!b) ∧ {e | e ∈ F} = M.E := by
--   obtain ⟨x, y, z, w, hxy, hxz, hxw, hyz, hyw, hzw, hE⟩ := encard_eq_four.1 h.encard_eq
--   refine ⟨[x, y, z, w], ?_, by simp [hE, Set.ext_iff]⟩
--   grind [isFan_four_iff, encard_eq_three, h.isTriangle_iff, h.bDual_eq_self]

-- lemma IsFan.contract_disjoint_aux (hF : M.IsFan F false c) (h4 : 4 ≤ F.length)
--     (hX : Disjoint {e | e ∈ F} X) (hb : F[0] ∉ M.closure X) (hXE : X ⊆ M.E):
--     (M ／ X).IsTriangle {F[0], F[1], F[2]} := by
--   have hT := hF.isTriangle_getElem_of_eq 0 (by lia) rfl
--   have hdj : Disjoint {F[0], F[1], F[2]} X := hX.mono_left <| (show _ ⊆ {e | e ∈ F} by grind)
--   rw [isTriangle_iff, and_iff_left hT.three_elements]
--   refine Skew.isCircuit_contract (by_contra fun hsk ↦ hb ?_) hT.isCircuit hdj.symm
--   rw [skew_comm] at hsk
--   obtain ⟨C, hC, hCss, h0C, hCX⟩ :=
--     hT.isCircuit.exists_isCircuit_mem_subset_union_of_not_skew hdj hsk (e := F[0]) (by simp)
--   have hT' := hF.isTriad_getElem_of_eq 1 (by lia) (by simp)
--   have h21 := hT'.reverse.mem_iff_mem_of_isCocircuit (K := C) (by simpa)
--     (by grind [hF.nodup.getElem_inj_iff])
--   by_cases h1 : F[1] ∈ C
--   · simp [← hT.isCircuit.eq_of_subset_isCircuit hC (by grind), hdj.inter_eq] at hCX
--   grw [← sdiff_subset_iff.2 hCss, ← union_singleton, ← sdiff_sdiff, Disjoint.sdiff_eq_left (a := C)
--     (by grind), hC.closure_sdiff_singleton_eq]
--   exact M.mem_closure_of_mem h0C

-- /- Contractions preserve the property of being a fan, unless one of the ends is a joint
-- spanned by the contract-set. -/
-- lemma IsFan.contract_disjoint (hF : M.IsFan F b c) (h4 : 4 ≤ F.length) (hX : Disjoint {e | e ∈ F} X)
--     (hb : b = false → F[0] ∉ M.closure X) (hc : c = false → F[F.length - 1] ∉ M.closure X) :
--     (M ／ X).IsFan F b c := by
--   wlog hXE : X ⊆ M.E generalizing X with aux
--   · grind [M.closure_inter_ground X, M.contract_inter_ground_eq X]
--   rw [isFan_iff_forall (by lia), hF.length_bodd_eq, and_iff_right rfl, and_iff_right hF.nodup]
--   rintro i hi
--   rw [isTriangle_iff, and_iff_left (hF.isTriangle_getElem i hi).three_elements]
--   obtain rfl | rfl := b.eq_or_eq_not !i.bodd
--   · simp only [Bool.not_bne, bne_self_eq_false, Bool.not_false, bDual_true, dual_contract,
--       delete_isCircuit_iff, disjoint_insert_left, disjoint_singleton_left,
--       (hF.isTriad_getElem_of_eq i hi (by simp)).isCircuit]
--     grind
--   obtain rfl | i := i
--   · simp only [Nat.bodd_zero, Bool.not_false, Bool.not_true, forall_const] at hb
--     simpa using (hF.contract_disjoint_aux h4 hX hb hXE).isCircuit
--   obtain heq | hlt := (show i + 4 ≤ F.length from hi).eq_or_lt
--   · obtain rfl : c = false := by simpa [← heq] using hF.bool_right_eq
--     have hT := (hF.reverse.contract_disjoint_aux (by simpa) (by simpa)
--       (by simpa using hc) hXE).reverse
--     simpa [← heq] using hT.isCircuit
--   simp only [Nat.bodd_succ, Bool.not_not, bne_self_eq_false, bDual_false]
--   have hT := hF.isTriangle_getElem_of_eq (i + 1) (by lia) (by simp)
--   have hTdj : Disjoint {F[i + 1], F[i + 1 + 1], F[i + 1 + 2]} X := by
--     simp only [disjoint_insert_left, disjoint_singleton_left]
--     grind
--   refine Skew.isCircuit_contract (by_contra fun hsk ↦ ?_) hT.isCircuit hTdj.symm
--   rw [skew_comm] at hsk
--   obtain ⟨C, hC, hCss, hCi, hCX⟩ := hT.isCircuit.exists_isCircuit_mem_subset_union_of_not_skew hTdj
--     (e := F[i + 2]) hsk (by simp) hXE
--   have hi1C : F[i + 1] ∈ C:= (hF.isTriad_getElem_of_eq i (by lia)
--     (by simp)).reverse.swap_right.mem_of_mem_of_notMem_of_is_Cocircuit (by simpa) hCi
--     (by grind [hF.nodup.getElem_inj_iff])
--   have hi3C : F[i + 3] ∈ C := (hF.isTriad_getElem_of_eq (i + 2) (by lia)
--     (by simp)).swap_right.mem_of_mem_of_notMem_of_is_Cocircuit (by simpa) hCi
--     (by grind [hF.nodup.getElem_inj_iff])
--   simp [← hT.isCircuit.eq_of_subset_isCircuit hC (by grind [insert_subset_iff]),
--     hTdj.inter_eq] at hCX

-- /-- If `N` is a minor of `M`, and `F` is a fan of `M` contained in `E(N)`, whose (co)joint ends are
-- are not (co)loops of `N`, then `F` is also a fan of `N`.  -/
-- lemma IsFan.minor {N : Matroid α} (hF : M.IsFan F b c) (h4 : 4 ≤ F.length) (hNM : N ≤m M)
--     (hFN : {e | e ∈ F} ⊆ N.E) (h_first : (N.bDual b).IsNonloop F[0])
--     (h_last : (N.bDual c).IsNonloop F[F.length - 1]) : N.IsFan F b c := by
--   obtain ⟨C, D, hC, hD, hCD, rfl⟩ := hNM.exists_eq_contract_delete_disjoint
--   have hCF := hF.contract_disjoint h4 (X := C) (by grind) ?_ ?_
--   · have hwin := (hCF.dual.contract_disjoint (X := D) h4 (by grind) ?_ ?_).dual
--     · simpa using hwin
--     · simp only [Bool.not_eq_eq_eq_not, Bool.not_false, dual_contract, delete_closure_eq, mem_sdiff,
--         not_and, not_not, hCD.sdiff_eq_right]
--       rintro rfl hcl
--       refine False.elim <| h_first.not_isLoop ?_
--       grind [bDual_true, dual_delete, dual_contract, contract_isLoop_iff_mem_closure,
--         delete_closure_eq, hCD.sdiff_eq_right]
--     simp only [Bool.not_eq_eq_eq_not, Bool.not_false, dual_contract, delete_closure_eq, mem_sdiff]
--     rintro rfl hcl
--     refine h_last.not_isLoop ?_
--     grind [bDual_true, dual_delete, dual_contract, contract_isLoop_iff_mem_closure,
--       delete_closure_eq]
--   · rintro rfl hcl
--     grind [bDual_false, delete_isLoop_iff, contract_isLoop_iff_mem_closure, h_first.not_isLoop]
--   rintro rfl hcl
--   grind [h_last.not_isLoop, bDual_false, delete_isLoop_iff, contract_isLoop_iff_mem_closure]

-- -- lemma Triassic.exists_fan (hM : M.Triassic) (hfin : M.Finite) (hne : M.Nonempty)
-- --     (hconn : M.TutteConnected 3) : ∃ F c, M.IsFan F false c ∧ {e | e ∈ F} = M.E := by
-- --   by_cases hU : M.IsFiniteRankUniform 2 4
-- --   · grind [hU.exists_isFan false]
-- --   suffices aux : ∀ (n : ℕ), n ≤ M.E.encard → ∃ F b, M.IsFan F b false ∧ n ≤ F.length
-- --   · have hcard := hfin.ground_finite.encard_eq_coe_toFinset_card
-- --     obtain ⟨F, b, hF, hle⟩ := aux _ hcard.symm.le
-- --     refine ⟨F.reverse, b, hF.reverse, ?_⟩
-- --     refine Finite.eq_of_subset_of_encard_le (by simp) hF.reverse.subset_ground ?_
-- --     simp only [mem_reverse]
-- --     rwa [hF.nodup.encard_toSet_eq, hcard, Nat.cast_le]
-- --   intro n hle
-- --   induction n with
-- --   | zero =>
-- --     obtain ⟨e, he⟩ := hne.ground_nonempty
-- --     obtain ⟨f, g, hefg⟩ := hM.exists_triangle_bDual he false
-- --     refine ⟨[e, f, g], false, hefg.isFan, by simp⟩
-- --   | succ n ih =>
-- --     obtain ⟨F, b, hF, hnF⟩ := ih (by grw [← hle]; simp)
-- --     generalize hc : false = c at hF
-- --     cases hF with
-- --     | of_pair b e f he hf hne =>
-- --       obtain ⟨x, y, hexy⟩ := hM.exists_triangle_bDual (he false).mem_ground (!b)
-- --       exact ⟨[e, x, y], (!b), hexy.isFan_of_bDual, by grind⟩
-- --     | cons_triangle e x y F b c h heF hT =>
-- --       subst hc
-- --       obtain ⟨p, q, hepq⟩ := hM.exists_triangle_bDual (by simpa using hT.mem_ground₁) b
-- --       have hmem := hepq.mem_or_mem_of_isCircuit_bDual hT.isCircuit (by simp)
-- --       wlog hp : p = x ∨ p = y generalizing p q with aux
-- --       · exact aux q p hepq.swap_right (by grind [hepq.ne₁₂]) (by grind [hepq.ne₁₂])
-- --       by_cases hq : q = x ∨ q = y
-- --       · have h_eq : ({e, p, q} : Set α) = {e, x, y} := by grind [hepq.ne₂₃]
-- --         contrapose! hU
-- --         exact (hepq.isFiniteRankUniform_two_four_of_isTriad (by simpa [h_eq])
-- --           (by simpa)).of_bDual_self
-- --       have := h.cons heF hT
-- --       obtain rfl | rfl := hp
-- --       · by_cases hqF : q ∈ F
-- --         · sorry
-- --         have hF' := (h.cons heF hT).cons (e := q) (by grind) <|
-- --           by simpa using hepq.reverse.swap_right
-- --         exact ⟨_, _, hF', by grind⟩
-- --       sorry


-- --       _












-- --           -- obtain ⟨E, hE4, hME⟩ := hepq.swap_right.eq_unifOn_two_four_of_isTriad_of_tutteConnected
-- --         obtain rfl | rfl := hp
-- --         · sorry
-- --         cases F with
-- --         | nil =>
-- --           obtain rfl | hne := eq_or_ne x q
-- --           · obtain ⟨E, hE4, hME⟩ := hepq.swap_right.eq_unifOn_two_four_of_isTriad_of_tutteConnected
-- --               (by simpa [IsTriad] using hT) (by simpa)
-- --             obtain ⟨F, hF, hFE⟩ := unifOn_two_four_isFan hE4 b
-- --             have hF : F.length = 4 := by
-- --               rw [← ENat.natCast_inj, ← hF.nodup.encard_toSet_eq, hFE, hE4, Nat.cast_ofNat]
-- --             apply_fun (Matroid.bDual · b) at hME
-- --             simp only [bDual_bDual, bne_self_eq_false, bDual_false] at hME
-- --             exact ⟨F.reverse, true, by simpa [hME], by grind⟩
-- --           have hF : M.IsFan [x, e, p, q] (!b) b := by simpa using
-- --             (hepq.isFan.cons (e := x) (by grind) (by simpa using hT.swap_left)).bDual b
-- --           cases b
-- --           · exact ⟨_, _, hF, by grind⟩
-- --           exact ⟨_, _, hF.reverse, by grind⟩
-- --         | cons z F =>
-- --           have := h.isTriangle_bDual sorry
-- --           simp at this


-- --     -- have := hM.exists_triangle_bDual

-- --     --  hfin.ground_finite.toFinset.card
-- --     --   (by simp [hfin.ground_finite.encard_eq_coe_toFinset_card])
