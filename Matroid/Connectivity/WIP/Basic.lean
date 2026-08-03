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

lemma Nat.two_mul_div2 (n : ℕ) (hn : n.bodd = false) : 2 * n.div2 = n := by
  nth_rw 1 [eq_comm, ← n.bodd_add_div2, hn, Bool.toNat_false, zero_add]

lemma Nat.two_mul_div2_add_one (n : ℕ) (hn : n.bodd = true) : 2 * n.div2 + 1 = n := by
  nth_rw 1 [eq_comm, ← n.bodd_add_div2, hn, Bool.toNat_true, add_comm]

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

@[grind =]
lemma Bool.toNat_add_toNat_bnot (b : Bool) : b.toNat + (!b).toNat = 1 := by
  cases b with simp

lemma Bool.beq_not (b c : Bool) : (b == !c) = (b != c) := by
  cases b with simp

lemma Bool.not_beq (b c : Bool) : ((!b) == c) = (b != c) := by
  cases b with simp

@[simp]
lemma Bool.not_beq_not (b c : Bool) : ((!b) == !c) = (b == c) := by
  cases b with simp

namespace Matroid

-- variable {J : Bool → List α}

variable {α : Type*} {M : Matroid α} {X Y C K T : Set α} {e f g x y : α} {b c d : Bool}
    {n i j : ℕ} {b b' c : Bool}

/-- A fan of a matroid `M` is a sequence `[e₀, f₀, e₁, f₁, ...]` of at least two
distinct elements of `M`, where consecutive triples alternate between being triangles and triads.
We allow fans to have length two for technical reasons; in a fan of length `2`, we
insist that neither element is a loop or coloop.

The fan may start and end with either triangles or triads;
if each pair of consecutive `eᵢ` belongs to a common triangle,
then the `eᵢ` are the 'joints' of the fan, and the `fᵢ` are 'cojoints'.

Formally, `M.Fan` is a type with a coercion to a list, also storing booleas variables `b c` are
boolean variables indicating whether the fan respectively starts and ends with a triangle.
We have `b = c` if and only if `J` had odd length.

For example, if `{e,f,g}` is a triangle of `M`, then the fan `e, f, g` corresponds to the
an `F : M.Fan` with `(F : List α) = [e, f, g]`, and `F.b = F.c = false`.
(The `false false` means that the fan begins and ends on joints.) -/
structure Fan (M : Matroid α) where
  toList : List α
  b : Bool
  c : Bool
  toList_nodup : toList.Nodup
  toList_length_ge : 2 ≤ toList.length
  toList_length_bodd : toList.length.bodd = (b == c)
  isNonloop' : toList.length = 2 → ∀ i (hi : i < toList.length) (d : Bool),
      (M.bDual d).IsNonloop toList[i]
  isTriangle' : ∀ i (hi : i + 2 < toList.length), (M.bDual (b != i.bodd)).IsTriangle
    {toList[i], toList[i + 1], toList[i + 2]}

namespace Fan

variable {F F' : M.Fan}

instance coeList : CoeOut M.Fan (List α) where coe F := F.toList

abbrev length (F : M.Fan) : ℕ := List.length (F : List α)

lemma length_bodd (F : M.Fan) : F.length.bodd = (F.b == F.c) := F.toList_length_bodd

@[grind! ., simp]
lemma left_beq_right (F : M.Fan) : (F.b == F.c) = F.length.bodd :=
  F.toList_length_bodd.symm

@[grind! ., simp]
lemma left_bne_right (F : M.Fan) : (F.b != F.c) = !F.length.bodd := by
  simp [← F.length_bodd, bne_eq]

@[grind! ., simp]
lemma left_beq_not_right (F : M.Fan) : ((!F.b) == F.c) = !F.length.bodd := by
  simp [Bool.not_beq]

@[grind! ., simp]
lemma not_left_beq_right (F : M.Fan) : (F.b == !F.c) = !F.length.bodd := by
  simp [Bool.beq_not]

lemma length_bodd_eq_false (F : M.Fan) (h_eq : F.b = !F.c) : F.length.bodd = false := by
  grind

lemma length_bodd_eq_true (F : M.Fan) (h_eq : F.b = F.c) : F.length.bodd = true := by
  grind

@[grind! .]
lemma length_ge_two (F : M.Fan) : 2 ≤ F.length :=
  F.toList_length_ge

@[simp]
lemma length_ne_one (F : M.Fan) : F.length ≠ 1 := by
  grind

@[grind! .]
lemma length_ge_three (F : M.Fan) (hb : F.b = F.c) : 3 ≤ F.length :=
  F.length_ge_two.eq_or_lt.elim (fun h ↦ by simpa [hb, F.length_bodd] using congr_arg Nat.bodd h) id

@[simp, grind=]
lemma length_toList (F : M.Fan) : F.toList.length = F.length := rfl

@[simp]
lemma toList_ne_nil (F : M.Fan) : (F : List α) ≠ [] := by
  grw [← length_pos_iff, length_toList, ← length_ge_two]
  simp

-- @[reducible]
instance : GetElem (M.Fan) Nat α (fun t i => i < t.length) where
  getElem := fun t i h => t.toList[i]

instance : Membership α (M.Fan) where mem F e := e ∈ (F : List α)

@[simp]
lemma getElem_toList' (F : M.Fan) (i : ℕ) {hi : i < F.length} : (F : List α)[i] = F[i] := rfl

@[simp]
lemma getElem_toList (F : M.Fan) (i : ℕ) {hi : i < (F : List α).length} :
    (F : List α)[i] = F[i] := rfl

macro_rules
  | `(tactic| get_elem_tactic_extensible) =>
    `(tactic| grind[List.length_rotate, Nat.add_one_lt_of_bodd_eq])

@[simp]
lemma toList_head (F : M.Fan) : F.toList.head (by simp) = F[0] := by
  rw [← getElem_toList', ← getElem_zero_eq_head (by grind)]

lemma right_eq (F : M.Fan) : F.c = (F.b == F.length.bodd) := by
  cases h : F.b with simp [F.length_bodd, h]

lemma left_eq (F : M.Fan) : F.b = (F.c == F.length.bodd) := by
  cases h : F.b with simp [h, F.length_bodd]

lemma right_eq_left (F : M.Fan) (hF : F.length.bodd = true) : F.c = F.b := by
  simp [F.left_eq, hF]

lemma right_eq_not (F : M.Fan) (hF : F.length.bodd = false) : F.c = !F.b := by
  simp [F.left_eq, hF]

lemma left_eq_not (F : M.Fan) (hF : F.length.bodd = false) : F.b = !F.c := by
  simp [F.left_eq, hF]

@[ext]
lemma ext {F F' : M.Fan} (h : (F : List α) = (F' : List α)) (hb : F.b = F'.b) : F = F' := by
  have hc : F.c = F'.c := by
    rw [F.right_eq, hb, F'.right_eq, ← length_toList, h]
  cases F with cases F' with grind

-- lemma toList_inj {F F' : M.Fan} (hF : (F : List α) = (F' : List α)) : F = F' := by
--   cases F with cases F' with grind

-- @[simp]
-- lemma toList_inj_iff {F F' : M.Fan} : (F : List α) = (F' : List α) ↔ (F = F') := by
--   cases F with cases F' with grind

@[ext (iff := false)]
protected lemma ext' {F F' : M.Fan} (h_length : F.length = F'.length) (hb : F.b = F'.b)
    (hi : ∀ i (hi : i < F.length) (hi' : i < F'.length), F[i] = F'[i]) : F = F' :=
  Fan.ext (List.ext_getElem h_length hi) hb

def toSet (F : M.Fan) : Set α := {e | e ∈ F}

instance coeSet : CoeOut (M.Fan) (Set α) where coe F := F.toSet

attribute [coe] Fan.toList Fan.toSet

initialize_simps_projections Fan (b → left, c → right)

@[simp]
lemma mem_toSet (F : M.Fan) : e ∈ (F : Set α) ↔ e ∈ F := Iff.rfl

@[simp]
lemma mem_toList (F : M.Fan) : e ∈ (F : List α) ↔ e ∈ F := Iff.rfl

@[simp]
lemma ofPred_mem_toList_eq (F : M.Fan) : {e | e ∈ (F : List α)} = F := rfl

@[simp]
lemma ofPred_mem_eq (F : M.Fan) : {e | e ∈ F} = F := rfl

@[simp]
lemma getElem_mem_toSet (F : M.Fan) (hi : i < F.length) : F[i] ∈ (F : Set α) :=
  getElem_mem hi

@[simp]
protected lemma nodup (F : M.Fan) : (F : List α).Nodup :=
  F.toList_nodup

@[simp]
lemma encard_toSet_eq (F : M.Fan) : (F : Set α).encard = F.length := by
  rw [← ofPred_mem_toList_eq, F.nodup.encard_toSet_eq, length_toList]

lemma toSet_nontrivial (F : M.Fan) : (F : Set α).Nontrivial := by
  grw [← two_le_encard_iff_nontrivial, encard_toSet_eq, ← F.length_ge_two, ENat.coe_eq_ofNat]

lemma getElem_of_mem (F : M.Fan) (heF : e ∈ F) : ∃ (i : ℕ) (hi : i < F.length), F[i] = e :=
  List.getElem_of_mem heF

@[simp]
lemma getElem_mem {hi : i < F.length} : F[i] ∈ F :=
  List.getElem_mem hi

@[simp, grind →]
lemma getElem_inj (F : M.Fan) {i j} {hi : i < F.length} {hj : j < F.length} :
    F[i] = F[j] ↔ i = j :=
  F.nodup.getElem_inj_iff

lemma isNonloop_bDual (F : M.Fan) {hi : i < F.length} {d : Bool} : (M.bDual d).IsNonloop F[i] := by
  obtain (h2 | h3) := F.length_ge_two.eq_or_lt
  · exact F.isNonloop' h2.symm i hi d
  obtain hi2 | hi3 := le_or_gt i 2
  · simpa using (F.isTriangle' 0 (by lia)).isNonloop_bDual_of_mem (e := F[i])
      (by simp [show i = 0 ∨ i = 1 ∨ i = 2 by lia]) (b := (F.b != d))
  obtain ⟨i, rfl⟩ := Nat.exists_eq_add_of_le' hi3.le
  simpa using (F.isTriangle' i hi).isNonloop_bDual₃ (b := (i.bodd != (F.b != d)))

lemma isNonloop (F : M.Fan) {hi : i < F.length} : M.IsNonloop F[i] :=
  F.isNonloop_bDual (d := false)

@[simp]
lemma isNonloop_bDual_of_mem {F : M.Fan} (heF : e ∈ F) (d : Bool) :
    (M.bDual d).IsNonloop e := by
  obtain ⟨i, hi, rfl⟩ := F.getElem_of_mem heF
  exact F.isNonloop_bDual

@[simp]
lemma isNonloop_of_mem {F : M.Fan} (heF : e ∈ F) : M.IsNonloop e :=
  F.isNonloop_bDual_of_mem (d := false) heF


lemma isTriangle (F : M.Fan) (i : ℕ) (hi : i + 2 < F.length) :
    (M.bDual (F.b != i.bodd)).IsTriangle {F[i], F[i + 1], F[i + 2]} :=
  F.isTriangle' i hi

lemma isTriangle_of_eq {F : M.Fan} (i : ℕ) (hi : i + 2 < F.length) (h_eq : i.bodd = F.b) :
    M.IsTriangle {F[i], F[i + 1], F[i + 2]} := by
  simpa [h_eq] using F.isTriangle i hi

lemma isTriangle_bDual_of_eq (F : M.Fan) (i : ℕ) (d : Bool) (hi : i + 2 < F.length)
    (hd : d = (F.b != i.bodd)) : (M.bDual d).IsTriangle {F[i], F[i + 1], F[i + 2]} := by
  subst d
  exact F.isTriangle i hi

lemma Bool.bnot_toNat (b : Bool) : (!b).toNat = 1 - b.toNat := by
  cases b with simp

-- lemma Nat.two_mul_div2 (n : ℕ) : 2 * n.div2 = n - n.bodd.toNat := by
--   refine Nat.eq_sub_of_add_eq ?_
--   rw [add_comm, n.bodd_add_div2]


/-- Copy a fan.  -/
@[simps]
def copy (F : M.Fan) (M' : Matroid α) (hM : M = M') : M'.Fan where
  toList := F
  b := F.b
  c := F.c
  toList_nodup := F.nodup
  toList_length_ge := F.toList_length_ge
  toList_length_bodd := F.toList_length_bodd
  isNonloop' := hM ▸ F.isNonloop'
  isTriangle' := hM ▸ F.isTriangle'

@[simp]
lemma copy_coeSet_eq (F : M.Fan) {M' : Matroid α} (hM : M = M') :
    (F.copy M' hM : Set α) = F := rfl

@[simp]
lemma copy_length (F : M.Fan) (M' : Matroid α) (hM : M = M') :
    (F.copy M' hM).length = F.length := rfl

@[simp]
lemma copy_getElem (F : M.Fan) (M' : Matroid α) (hM : M = M') (i : ℕ)
    {hi : i < (F.copy M' hM).length} :
    (F.copy M' hM)[i] = F[i]'(show i < F.length from hi) := rfl

@[simp]
lemma copy_eq_self (F : M.Fan) : F.copy M rfl = F := rfl

/-- Add an element to the beginning of a fan. -/
@[simps]
protected def cons (F : M.Fan) (heF : e ∉ F) (hT : (M.bDual !F.b).IsTriangle {e, F[0], F[1]}) :
    M.Fan where
  toList := e :: F
  b := !F.b
  c := F.c
  toList_nodup := by simpa
  toList_length_ge := by grind
  toList_length_bodd := by simp
  isNonloop' h := by simp at h
  isTriangle' := by
    rintro (rfl | i) hi
    · simpa
    simpa using! F.isTriangle i (by grind)

@[simp]
lemma cons_length (F : M.Fan) (heF : e ∉ F) (hT) :
    (F.cons heF hT).length = F.length + 1 := by
  simp [← length_toList]

@[simp]
lemma cons_toSet (F : M.Fan) (heF : e ∉ F) (hT) :
    (F.cons heF hT : Set α) = insert e (F : Set α) := by
  rw [← ofPred_mem_toList_eq]
  simp [mem_cons, mem_toList, ofPred_or]

@[simp]
lemma getElem_cons_zero (F : M.Fan) (heF : e ∉ F) (hT) :
    (F.cons heF hT)[0] = e := rfl

@[simp]
lemma getElem_cons_succ (F : M.Fan) (heF : e ∉ F) (hT) (hi : i + 1 < (F.cons heF hT).length) :
    (F.cons heF hT)[i + 1] = F[i]'(by simpa using hi) := rfl

abbrev getLast (F : M.Fan) : α := (F : List α).getLast F.toList_ne_nil

abbrev getPenult (F : M.Fan) : α := F[F.length - 2]

lemma subset_ground (F : M.Fan) : (F : Set α) ⊆ M.E :=
  fun _ he ↦ (F.isNonloop_of_mem he).mem_ground

lemma getLast_eq_getElem (F : M.Fan) : F.getLast = F[F.length - 1] :=
  List.getLast_eq_getElem _

@[simp]
lemma getElem_eq_getLast_iff (F : M.Fan) {hi : i < F.length} :
    F[i] = F.getLast ↔ i + 1 = F.length := by
  simp only [getLast_eq_getElem, getElem_inj]
  lia

@[simp]
lemma getLast_eq_getElem_iff (F : M.Fan) {hi : i < F.length} :
    F.getLast = F[i] ↔ i + 1 = F.length := by
  rw [eq_comm]
  simp

@[simp]
lemma getLast_ne_get_zero (F : M.Fan) : F.getLast ≠ F[0] := by
  simp [getLast_eq_getElem, show F.length - 1 ≠ 0 by grind]

@[simp]
lemma get_mem_ground (F : M.Fan) (i : ℕ) {hi : i < F.length} : F[i] ∈ M.E :=
  F.isNonloop.mem_ground

@[simp]
lemma mem_toList_getElems_iff (F : M.Fan) (i : ℕ) {hi : i < F.length} {s : Set ℕ} :
    F[i] ∈ (F : List α).getElems s ↔ i ∈ s :=
  F.nodup.getElem_mem_getElems_iff

/-- The fan with the same elements in reverse order. -/
@[simps]
def reverse (F : M.Fan) : M.Fan where
  toList := (F : List α).reverse
  b := F.c
  c := F.b
  toList_nodup := List.nodup_reverse.2 F.nodup
  toList_length_ge := by simp [F.length_ge_two]
  toList_length_bodd := by simp [Bool.beq_comm]
  isNonloop' hl i hi d := by
    simp only [getElem_reverse, length_toList, getElem_toList]
    exact F.isNonloop_bDual
  isTriangle' i hi := by
    simp only [getElem_reverse, length_toList, getElem_toList]
    simp only [length_reverse, length_toList] at hi
    convert (F.isTriangle (i := F.length - i - 3) (by lia)).reverse using 1
    · rw [Nat.sub_sub, Nat.bodd_sub (by lia), F.length_bodd, Nat.bodd_add]
      cases F.b with cases F.c with simp
    grind

@[simp]
lemma reverse_toSet (F : M.Fan) : (F.reverse : Set α) = F := by
  rw [← ofPred_mem_toList_eq]
  simp

@[simp, grind! .]
lemma reverse_length (F : M.Fan) : F.reverse.length = F.length := by
  exact length_reverse ..

@[simp]
lemma mem_reverse (F : M.Fan) : e ∈ F.reverse ↔ e ∈ F :=
  List.mem_reverse

@[simp]
lemma reverse_reverse (F : M.Fan) : F.reverse.reverse = F :=
  Fan.ext (by simp) (by simp)

@[simp]
lemma reverse_inj_iff : F.reverse = F'.reverse ↔ F = F' := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  rw [← F.reverse_reverse, h, F'.reverse_reverse]

alias ⟨reverse_inj, _⟩ := reverse_inj_iff

@[simp]
lemma reverse_getElem_zero (F : M.Fan) : F.reverse[0] = F.getLast := by
  simp_rw [getLast, ← getElem_toList', reverse_toList, List.getElem_reverse, tsub_zero,
    getElem_length_sub_one_eq_getLast]

@[simp]
lemma reverse_getElem_one (F : M.Fan) : F.reverse[1] = F.getPenult := by
  simp_rw [getPenult, ← getElem_toList, reverse_toList, List.getElem_reverse, Nat.sub_sub]

@[simp]
lemma reverse_getLast (F : M.Fan) : F.reverse.getLast = F[0] := by
  simp_rw [getLast, reverse_toList, getLast_reverse, toList_head]

@[simp]
lemma reverse_getPenult (F : M.Fan) : F.reverse.getPenult = F[1] := by
  rw [← F.reverse_reverse, reverse_getElem_one, reverse_reverse]

lemma reverse_getElem (F : M.Fan) (hi : i < F.reverse.length) :
    F.reverse[i] = F[F.length - 1 - i] := by
  rw [← getElem_toList]
  simp

lemma getElem_eq_reverse_getElem (F : M.Fan) (hi : i < F.length) :
    F[i] = F.reverse[F.length - 1 - i] := by
  grind [reverse_getElem]

/-- Add a new element to the end of a fan. -/
@[simps! left right]
def concat (F : M.Fan) (heF : e ∉ F) (hT : (M.bDual !F.c).IsTriangle {F.getPenult, F.getLast, e}) :
    M.Fan := (F.reverse.cons (e := e) (by simpa) (by simpa using hT.reverse)).reverse

@[simp]
lemma concat_toList (F : M.Fan) (heF : e ∉ F) (hT) :
    (F.concat heF hT).toList = F.toList ++ [e] := by
  simp [concat]

@[simp, grind! .]
lemma concat_length (F : M.Fan) {heF : e ∉ F} {hT} : (F.concat heF hT).length = F.length + 1 := by
  simp [concat]

lemma concat_getElem_of_lt (F : M.Fan) {heF : e ∉ F} {hT} {i}
    (hi : i < F.length) : (F.concat heF hT)[i] = F[i] := by
  simp_rw [← getElem_toList, concat_toList, getElem_append_left hi]

@[simp]
lemma concat_getElem_length (F : M.Fan) {heF : e ∉ F} {hT} : (F.concat heF hT)[F.length] = e := by
  simp [← getElem_toList, concat_toList]

/-- A fan gives a fan in any dual. -/
@[simps!]
def bDual (F : M.Fan) (d : Bool) : (M.bDual d).Fan where
  toList := F
  b := F.b != d
  c := F.c != d
  toList_nodup := F.nodup
  toList_length_ge := F.length_ge_two
  toList_length_bodd := by cases d with simp
  isNonloop' hl i hi d' := by simpa using F.isNonloop_bDual
  isTriangle' i hi := by cases d with simpa using! F.isTriangle i hi

/-- A fan of any dual gives a fan -/
@[simps!] def ofbDual (F : (M.bDual d).Fan) : M.Fan := (F.bDual d).copy _ (by simp)

@[simp] lemma bDual_length (F : M.Fan) (d : Bool) : (F.bDual d).length = F.length := rfl
@[simp] lemma bDual_toSet (F : M.Fan) (d : Bool) : (F.bDual d : Set α) = F := rfl
@[simp] lemma bDual_getElem (F : M.Fan) (d : Bool) (i : ℕ) (hi : i < (F.bDual d).length) :
    (F.bDual d)[i] = F[i] := rfl
@[simp] lemma mem_bDual (F : M.Fan) (d : Bool) : x ∈ F.bDual d ↔ x ∈ F := Iff.rfl

@[simp] lemma bDual_false (F : M.Fan) : F.bDual false = F := Fan.ext rfl (by simp)
@[simp] lemma bDual_getLast (F : M.Fan) : (F.bDual d).getLast = F.getLast := rfl

lemma bDual_cons (F : M.Fan) (d : Bool) {e : α} {he hT} :
    (F.cons (e := e) he hT).bDual d = (F.bDual d).cons (e := e) (by simpa) (by simpa) :=
  Fan.ext (by simp) <| by simp

@[simps!]
def dual (F : M.Fan) : M✶.Fan := (F.bDual true).copy M✶ rfl

@[simp] lemma dual_length (F : M.Fan) : F.dual.length = F.length := rfl
@[simp] lemma dual_toSet (F : M.Fan) : (F.dual : Set α) = F := rfl
@[simp] lemma dual_getElem (F : M.Fan) (i : ℕ) (hi : i < (F.dual).length) : F.dual[i] = F[i] := rfl
@[simp] lemma mem_dual (F : M.Fan) : x ∈ F.dual ↔ x ∈ F := Iff.rfl
@[simp] lemma dual_getLast (F : M.Fan) : F.dual.getLast = F.getLast := rfl
@[simp] lemma dual_getPenult (F : M.Fan) : F.dual.getPenult = F.getPenult := rfl
@[simp] lemma bDual_true (F : M.Fan) : F.bDual true = F.dual := rfl

@[reducible] def ofDual (F : M✶.Fan) : M.Fan := (F.bDual true).copy M (by simp)


/-- The length-2 fan given by a pair of non-loop, non-coloop elements. -/
@[simps]
def ofPair (he : ∀ i, (M.bDual i).IsNonloop e) (hf : ∀ i, (M.bDual i).IsNonloop f) (hef : e ≠ f)
    (b : Bool) : M.Fan where
  toList := [e, f]
  b := b
  c := !b
  toList_nodup := by simpa
  toList_length_ge := by simp
  toList_length_bodd := by simp
  isNonloop' := by grind [Nat.le_one_iff_eq_zero_or_eq_one]
  isTriangle' := by simp

@[simp]
lemma toSet_ofPair (he : ∀ i, (M.bDual i).IsNonloop e) (hf : ∀ i, (M.bDual i).IsNonloop f)
    (hef : e ≠ f) (b : Bool) : (Fan.ofPair he hf hef b : Set α) = {e, f} := by
  simp [← ofPred_mem_toList_eq, ofPred_or, pair_comm]

@[simp]
lemma length_ofPair (he : ∀ i, (M.bDual i).IsNonloop e) (hf : ∀ i, (M.bDual i).IsNonloop f)
    (hef : e ≠ f) (b) : (Fan.ofPair he hf hef b).length = 2 := rfl

lemma getElem_ofPair {he : ∀ i, (M.bDual i).IsNonloop e} {hf} {hef : e ≠ f} {b}
    {hi : i < (ofPair he hf hef b).length} : (ofPair he hf hef b)[i] = if i = 0 then e else f := by
  change [e,f][i] = _
  grind

@[simp]
lemma bDual_ofPair {he hf} {hef : e ≠ f} {b d} : (ofPair (M := M) he hf hef b).bDual d =
    ofPair (fun i ↦ by simpa using he _) (fun i ↦ by simpa using hf _) hef (b != d) :=
  Fan.ext (by simp) rfl

@[simp]
lemma reverse_ofPair (he : ∀ d, (M.bDual d).IsNonloop e) (hf : ∀ d, (M.bDual d).IsNonloop f)
    (hef : e ≠ f) (b) : (ofPair he hf hef b).reverse = (ofPair hf he hef.symm (!b)) :=
  Fan.ext (by simp) (by simp)

@[simp]
lemma cons_reverse (F : M.Fan) (heF : e ∉ F) (hT) : (F.cons heF hT).reverse =
    F.reverse.concat (by simpa) (by simpa using hT.reverse) :=
  Fan.ext (by simp [concat_toList]) <| by simp

lemma concat_reverse (F : M.Fan) (heF : e ∉ F) (hT) :
    (F.concat heF hT).reverse = F.reverse.cons (by simpa) (by simpa using hT.reverse) :=
  reverse_inj <| by simp

lemma eq_of_length_le_two (hF : F.length ≤ 2) : ∃ (e f : α) (b : Bool)
    (he : ∀ i, (M.bDual i).IsNonloop e) (hf : ∀ i, (M.bDual i).IsNonloop f) (hef : e ≠ f),
    F = Fan.ofPair he hf hef b := by
  replace hF := hF.antisymm F.length_ge_two
  refine ⟨F[0], F[1], F.b, fun _ ↦ F.isNonloop_bDual, fun _ ↦ F.isNonloop_bDual, by simp,
    Fan.ext' (by simpa) rfl ?_⟩
  simp +contextual [getElem_ofPair, Nat.le_one_iff_eq_zero_or_eq_one, or_imp]

/-- The length-3 fan given by a triangle. -/
@[simps]
def ofTriangle (hT : M.IsTriangle {e, f, g}) : M.Fan where
  toList := [e, f, g]
  b := false
  c := false
  toList_nodup := by simp [hT.ne₁₂, hT.ne₁₃, hT.ne₂₃]
  toList_length_ge := by simp
  toList_length_bodd := by simp
  isNonloop' := by simp
  isTriangle' := by
    rintro (rfl | i) hi
    · simpa
    simp [add_assoc] at hi

/-- The length-3 fan given by a triangle in some dual. -/
@[simps!, reducible]
def ofTriangle_bDual (h : (M.bDual b).IsTriangle {e, f, g}) : M.Fan :=
  (ofTriangle h).ofbDual.copy _ rfl

lemma length_sub_one_bodd_eq (F : M.Fan) : (F.length - 1).bodd = (F.b != F.c) := by
  rw [Nat.bodd_sub (by grind)]
  simp

lemma IsFan.mod_lt_length (F : M.Fan) (i : ℕ) : i % F.length < F.length :=
  Nat.mod_lt i (by grind)

/-- Remove the element at the start of a fan. -/
@[simps]
def tail (F : M.Fan) (hF : 3 ≤ F.length) : M.Fan where
  b := !F.b
  c := F.c
  toList := (F : List α).tail
  toList_nodup := F.nodup.tail
  toList_length_ge := by grind
  toList_length_bodd := by
    simp only [length_tail, length_toList, F.length_sub_one_bodd_eq]
    cases F.b with cases F.c with simp
  isNonloop' hl i hi d := by simpa using F.isNonloop_bDual (i := i + 1) (d := d)
  isTriangle' i hi := by simpa using F.isTriangle (i := i + 1) (by grind)

@[simp, grind! .]
lemma length_tail_add_one (F : M.Fan) (hF : 3 ≤ F.length) : (F.tail hF).length + 1 = F.length :=
  List.length_tail_add_one _ <| by grind

lemma length_tail (F : M.Fan) (hF) : (F.tail hF).length = F.length - 1 := by
  rw [← Nat.add_one_inj, length_tail_add_one, Nat.sub_add_cancel (by lia)]

@[simp]
lemma tail_toSet (F : M.Fan) {hF} : (F.tail hF : Set α) = (F : Set α) \ {F[0]} := by
  change {e | e ∈ (F : List α).tail} = _
  simp [F.nodup.toSet_tail_eq (by simp)]

@[simp]
lemma getElem_tail (F : M.Fan) (hF : 3 ≤ F.length) (hi : i < (F.tail hF).length) :
    (F.tail hF)[i] = F[i + 1]' (show i + 1 < F.length
      by rwa [← add_lt_add_iff_right (a := 1), length_tail_add_one] at hi) := by
  exact List.getElem_tail _

@[simp]
lemma getElem_mem_tail_iff (F : M.Fan) (hF : 3 ≤ F.length) (hi : i < F.length) :
    F[i] ∈ F.tail hF ↔ i ≠ 0 := by
  obtain rfl | i := i
  · exact iff_of_false (fun h0t ↦ by simpa using (F.tail hF).getElem_of_mem h0t) (by simp)
  rw [← F.getElem_tail hF _]
  · simpa using getElem_mem
  grind

lemma eq_tail_cons (F : M.Fan) (hF : 3 ≤ F.length) :
    F = (F.tail hF).cons (e := F[0]) (by simp) (by simpa using F.isTriangle 0 (by lia)) := by
  refine Fan.ext ?_ <| by simp
  rw [cons_toList, tail_toList, ← getElem_toList, getElem_zero_eq_head, cons_head_tail]

@[simp]
lemma cons_tail_eq (F : M.Fan) (he : e ∉ F) (hT : (M.bDual !F.b).IsTriangle {e, F[0], F[1]}) :
    (F.cons he hT).tail (by grw [cons_length, ← F.length_ge_two]) = F  :=
  Fan.ext (by simp) <| by simp

@[simp]
lemma getLast_tail (F : M.Fan) (hF : 3 ≤ F.length) : (F.tail hF).getLast = F.getLast := by
  rw [getLast_eq_getElem, getLast_eq_getElem, getElem_tail, getElem_inj, ← Nat.sub_add_comm
    (by grind), length_tail_add_one]

@[simp]
lemma getPenult_tail (F : M.Fan) (hF : 3 ≤ F.length) : (F.tail hF).getPenult = F.getPenult := by
  rw [getPenult, getPenult, getElem_tail, getElem_inj, ← Nat.sub_add_comm
    (by grind), length_tail_add_one]

/-- Remove the element at the end of a fan. -/
@[simps!]
def dropLast (F : M.Fan) (hF : 3 ≤ F.length) : M.Fan := (F.reverse.tail (by simpa)).reverse

lemma tail_reverse (F : M.Fan) (hF : 3 ≤ F.length) :
    (F.tail hF).reverse = F.reverse.dropLast (by simpa) := by
  simp [dropLast]

lemma dropLast_reverse (F : M.Fan) (hF : 3 ≤ F.length) :
    (F.dropLast hF).reverse = F.reverse.tail (by simpa) := by
  rw [dropLast, reverse_reverse]

@[simp, grind! .]
lemma length_dropLast_add_one (F : M.Fan) (hF : 3 ≤ F.length) :
    (F.dropLast hF).length + 1 = F.length := by
  simp [dropLast]

lemma length_dropLast (F : M.Fan) (hF : 3 ≤ F.length) :
    (F.dropLast hF).length = F.length - 1 := by
  rw [← F.length_dropLast_add_one hF, Nat.add_sub_cancel]

@[simp]
lemma dropLast_toSet (F : M.Fan) {hF} : (F.dropLast hF : Set α) = (F : Set α) \ {F.getLast} := by
  simp [dropLast]

@[simp]
lemma getElem_dropLast (F : M.Fan) (hF : 3 ≤ F.length)
    (hi : i < (F.dropLast hF).length) : (F.dropLast hF)[i] = F[i] := by
  rw! [← getElem_toList, dropLast_toList, List.getElem_dropLast, getElem_toList]
  rfl

@[simp]
lemma getElem_mem_dropLast_iff (F : M.Fan) (hF : 3 ≤ F.length) (hi : i < F.length) :
    F[i] ∈ F.dropLast hF ↔ i + 1 < F.length := by
  rw [dropLast, getElem_eq_reverse_getElem, mem_reverse, getElem_mem_tail_iff, ne_eq,
    Nat.sub_sub, Nat.sub_eq_zero_iff_le, not_le, add_comm]

lemma concat_dropLast (F : M.Fan) (hF : 3 ≤ F.length) :
    F = (F.dropLast hF).concat (e := F.getLast)
      (by simp [getLast_eq_getElem, Nat.sub_add_cancel (show 1 ≤ F.length by lia)])
      (by
        simp only [dropLast_right, Bool.not_not, getElem_dropLast, length_dropLast,
          getLast_eq_getElem, Nat.sub_sub]
        convert F.isTriangle (F.length - 3) (by lia)
        · simp [Nat.bodd_sub hF, F.right_eq]
        all_goals lia) := by
  rw [← reverse_inj_iff]
  simp_rw [concat_reverse, dropLast_reverse]
  convert F.reverse.eq_tail_cons (by simpa)
  simp

lemma dropLast_concat (F : M.Fan) (he : e ∉ F) (hT ) :
    (F.concat he hT).dropLast (by grw [concat_length, ← F.length_ge_two]) = F :=
  Fan.ext (by simp) <| by simp

@[elab_as_elim]
protected lemma induction {motive : ∀ {M : Matroid α} (_F : M.Fan), Prop}
    (pair : ∀ e f b (he : ∀ d : Bool, (M.bDual d).IsNonloop e)
      (hf : ∀ d : Bool, (M.bDual d).IsNonloop f) (hef : e ≠ f), motive (Fan.ofPair he hf hef b))
    (cons : ∀ (F₀ : M.Fan) (e : α) (heF₀ : e ∉ F₀)
      (hT : (M.bDual (!F₀.b)).IsTriangle {e, F₀[0], F₀[1]}) (_ih : motive F₀),
      motive (F₀.cons heF₀ hT)) (F : M.Fan) : motive F := by
  induction hi : F.length using Nat.strong_induction_on generalizing F with | h n ih =>
  subst n
  obtain h2 | h3 := F.length_ge_two.eq_or_lt
  · obtain ⟨e, f, b, he, hf, hef, rfl, rfl⟩ := F.eq_of_length_le_two h2.ge
    apply pair
  have hwin := cons (F.tail (by lia)) F[0] (by simp) (by simpa using F.isTriangle 0 (by lia))
    <| ih _ (by grind) _ rfl
  rwa [F.eq_tail_cons (by lia)]

-- /-- A constructor for length at least `3` without the `IsNonloop` obligation for-/
-- @[simps]
-- def ofList (L : List α) (b c : Bool) (hlen : 2 ≤ L.length) (hnd : L.Nodup)
--     (hFbc : L.length.bodd = (b == c))
--     (hnl : ∀ (hl : L.length = 2) d i (hi : i < 2), (M.bDual d).IsNonloop L[i])
--     (hL : ∀ i (hi : i + 2 < L.length),
--       (M.bDual (b != i.bodd)).IsTriangle {L[i], L[i + 1], L[i + 2]}) : M.Fan where
--   toList := L
--   b := b
--   c := c
--   toList_nodup := hnd
--   toList_length_ge := by lia
--   toList_length_bodd := hFbc
--   isTriangle' := hL
--   isNonloop' i hi d := by
--     match i with
--     | i + 2 =>
--       have hwin := (hL i hi).isNonloop_bDual₃ (b := ((d == i.bodd) == b))
--       cases b with | _ => simpa using hwin
--     | 0 => simpa using (hL 0 (by lia)).isNonloop_bDual₁ (b := b != d)
--     | 1 => simpa using (hL 0 (by lia)).isNonloop_bDual₂ (b := b != d)



    -- have := aux (X := X ∩ M.E) (by grind)


  -- refine IsTriangle.c



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
--       · grw [eRk_le_encard, ofPred_three, hT.three_elements, h.right_eq,
--           show (2 : ℕ∞) * 3 ≤ 3 + 1 + 1 + 1 from rfl.le]
--         simp
--       grw [ofPred_three, IsTriangle.eRk (by simpa using hT), h.right_eq,
--         show (2 : ℕ∞) * 2 ≤ 3 + 1 from rfl.le]
--       simp
--     | cons p F =>
--       simp_rw [List.mem_cons (b := e), ofPred_or, ofPred_eq_eq_singleton, singleton_union]
--       cases b
--       · grw [eRk_insert_le_add_one, mul_add, ih (by grind)]
--         simp [h.right_eq]
--         enat_to_nat! <;> lia
--       grw [← eRk_closure_eq, closure_insert_eq_of_mem_closure, eRk_closure_eq, ih (by grind)]
--       · simp [h.right_eq]
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
--   · obtain rfl : c = false := by simpa [← heq] using hF.right_eq
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
