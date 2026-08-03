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

@[grind =]
lemma Bool.toNat_add_toNat_bnot (b : Bool) : b.toNat + (!b).toNat = 1 := by
  cases b with simp

namespace Matroid

-- variable {J : Bool → List α}

variable {α : Type*} {M : Matroid α} {X Y C K T : Set α} {e f g x y : α} {b c d : Bool}
    {J : Bool → List α} {L : List α} {n i j : ℕ} {J : List α} {b b' c : Bool} {L : List ℕ}

/-- A structure -/
structure Fan (M : Matroid α) (b c : Bool) where
  toList : List α
  toList_nodup : toList.Nodup
  toList_length_ge : 2 ≤ toList.length
  toList_length_bodd : toList.length.bodd = (b == c)
  isNonloop' : ∀ i (hi : i < toList.length) (d : Bool), (M.bDual d).IsNonloop toList[i]
  isTriangle' : ∀ i (hi : i + 2 < toList.length), (M.bDual (b != i.bodd)).IsTriangle
    {toList[i], toList[i + 1], toList[i + 2]}

namespace Fan

variable {F F' : M.Fan b c}

instance coeList : CoeOut (M.Fan b c) (List α) where coe F := F.toList

abbrev length (F : M.Fan b c) : ℕ := List.length (F : List α)

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

@[simp]
lemma length_ne_one (F : M.Fan b c) : F.length ≠ 1 := by
  grind

@[grind! .]
lemma length_ge_three (F : M.Fan b b) : 3 ≤ F.length :=
  F.length_ge_two.eq_or_lt.elim (fun h ↦ by simpa [F.length_bodd] using congr_arg Nat.bodd h) id

@[simp, grind=]
lemma length_toList (F : M.Fan b c) : F.toList.length = F.length := rfl

@[simp]
lemma toList_ne_nil (F : M.Fan b c) : (F : List α) ≠ [] := by
  grw [← length_pos_iff, length_toList, ← length_ge_two]
  simp

-- @[reducible]
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

lemma toList_inj {F F' : M.Fan b c} (hF : (F : List α) = (F' : List α)) : F = F' := by
  cases F with cases F' with grind

@[simp]
lemma toList_inj_iff {F F' : M.Fan b c} : (F : List α) = (F' : List α) ↔ F = F' := by
  cases F with cases F' with grind

@[ext (iff := false)]
protected lemma ext {F F' : M.Fan b c} (h_length : F.length = F'.length)
    (hi : ∀ i (hi : i < F.length) (hi' : i < F'.length), F[i] = F'[i]) : F = F' :=
  toList_inj <| List.ext_getElem h_length hi

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

lemma bool_right_eq (F : M.Fan b c) : c = (b == F.length.bodd) := by
  simp [F.length_bodd]

lemma bool_left_eq (F : M.Fan b c) : b = (c == F.length.bodd) := by
  cases b with simp [F.length_bodd]

lemma isNonloop_bDual (F : M.Fan b c) {hi : i < F.length} {d : Bool} : (M.bDual d).IsNonloop F[i] :=
  F.isNonloop' i hi d

lemma isNonloop (F : M.Fan b c) {hi : i < F.length} : M.IsNonloop F[i] :=
  F.isNonloop_bDual (d := false)

lemma getElem_of_mem (F : M.Fan b c) (heF : e ∈ F) : ∃ (i : ℕ) (hi : i < F.length), F[i] = e :=
  List.getElem_of_mem heF

@[simp]
lemma getElem_mem {hi : i < F.length} : F[i] ∈ F :=
  List.getElem_mem hi

@[simp]
lemma isNonloop_bDual_of_mem {F : M.Fan b c} (heF : e ∈ F) (d : Bool) :
    (M.bDual d).IsNonloop e := by
  obtain ⟨i, hi, rfl⟩ := F.getElem_of_mem heF
  exact F.isNonloop_bDual

@[simp]
lemma isNonloop_of_mem {F : M.Fan b c} (heF : e ∈ F) : M.IsNonloop e :=
  F.isNonloop_bDual_of_mem (d := false) heF

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


/-- Copy a fan.  -/
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
    (F.copy M' b' c' hM hb hc)[i] = F[i]'(show i < F.length from hi) := rfl

@[simp]
lemma copy_eq_self (F : M.Fan b c) : F.copy M b c rfl rfl rfl = F := rfl

/-- Add an element to the beginning of a fan. -/
@[simps]
protected def cons (F : M.Fan b c) (heF : e ∉ F) (hT : (M.bDual !b).IsTriangle {e, F[0], F[1]})
    (b' : Bool := !b) (hb : b' = !b := by simp) : M.Fan b' c where
  toList := e :: F
  toList_nodup := by simpa
  toList_length_ge := by grind
  toList_length_bodd := by
    simp [F.length_bodd, hb]
    cases b' with grind
  isNonloop' := by
    rintro (rfl | i) hi d
    · simpa [hb] using hT.isNonloop_bDual₁ (b := (b == d))
    simpa using F.isNonloop_bDual
  isTriangle' := by
    rintro (rfl | i) hi
    · simpa [hb]
    simpa [hb] using! F.isTriangle i (by grind)

@[simp]
lemma cons_length (F : M.Fan b c) (heF : e ∉ F) (hT) {b' hb'} :
    (F.cons heF hT b' hb').length = F.length + 1 := by
  simp [← length_toList]

@[simp]
lemma cons_toSet (F : M.Fan b c) (heF : e ∉ F) (hT) {hb : b' = !b}:
    (F.cons heF hT b' hb : Set α) = insert e (F : Set α) := by
  rw [← ofPred_mem_toList_eq]
  simp [mem_cons, mem_toList, ofPred_or]

@[simp]
lemma getElem_cons_zero (F : M.Fan b c) (heF : e ∉ F) (hT) (hb : b' = !b) :
    (F.cons heF hT b' hb)[0] = e := rfl

@[simp]
lemma getElem_cons_succ (F : M.Fan b c) (heF : e ∉ F) (hT) {hb : b' = !b}
    (hi : i + 1 < (F.cons heF hT b' hb).length) :
    (F.cons heF hT b' hb)[i + 1] = F[i]'(by simpa using hi) := rfl

abbrev getLast (F : M.Fan b c) : α := (F : List α).getLast F.toList_ne_nil

abbrev getPenult (F : M.Fan b c) : α := F[F.length - 2]

lemma subset_ground (F : M.Fan b c) : (F : Set α) ⊆ M.E :=
  fun _ he ↦ (F.isNonloop_of_mem he).mem_ground

lemma getLast_eq_getElem (F : M.Fan b c) : F.getLast = F[F.length - 1] :=
  List.getLast_eq_getElem _

@[simp]
lemma getElem_eq_getLast_iff (F : M.Fan b c) {hi : i < F.length} :
    F[i] = F.getLast ↔ i + 1 = F.length := by
  simp only [getLast_eq_getElem, getElem_inj]
  lia

@[simp]
lemma getLast_ne_get_zero (F : M.Fan b c) : F.getLast ≠ F[0] := by
  simp [getLast_eq_getElem, show F.length - 1 ≠ 0 by grind]

@[simp]
lemma get_mem_ground (F : M.Fan b c) (i : ℕ) {hi : i < F.length} : F[i] ∈ M.E :=
  F.isNonloop.mem_ground

@[simp]
lemma mem_toList_getElems_iff (F : M.Fan b c) (i : ℕ) {hi : i < F.length} {s : Set ℕ} :
    F[i] ∈ (F : List α).getElems s ↔ i ∈ s :=
  F.nodup.getElem_mem_getElems_iff

/-- The fan with the same elements in reverse order. -/
@[simps]
def reverse {b c : Bool} (F : M.Fan b c) : M.Fan c b where
  toList := (F : List α).reverse
  toList_nodup := List.nodup_reverse.2 F.nodup
  toList_length_ge := by simp [F.length_ge_two]
  toList_length_bodd := by simp [F.length_bodd, eq_comm]
  isNonloop' i hi d := by
    simp only [getElem_reverse, length_toList, getElem_toList]
    exact F.isNonloop_bDual
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

@[simp, grind! .]
lemma reverse_length (F : M.Fan b c) : F.reverse.length = F.length := by
  exact length_reverse ..

@[simp]
lemma mem_reverse (F : M.Fan b c) : e ∈ F.reverse ↔ e ∈ F :=
  List.mem_reverse

@[simp]
lemma reverse_reverse (F : M.Fan b c) : F.reverse.reverse = F :=
  toList_inj <| by simp

@[simp]
lemma reverse_inj_iff : F.reverse = F'.reverse ↔ F = F' := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  rw [← F.reverse_reverse, h, F'.reverse_reverse]

alias ⟨reverse_inj, _⟩ := reverse_inj_iff

@[simp]
lemma reverse_getElem_zero (F : M.Fan b c) : F.reverse[0] = F.getLast := by
  simp_rw [getLast, ← getElem_toList', reverse_toList, List.getElem_reverse, tsub_zero,
    getElem_length_sub_one_eq_getLast]

@[simp]
lemma reverse_getElem_one (F : M.Fan b c) : F.reverse[1] = F.getPenult := by
  simp_rw [getPenult, ← getElem_toList, reverse_toList, List.getElem_reverse, Nat.sub_sub]

@[simp]
lemma reverse_getLast (F : M.Fan b c) : F.reverse.getLast = F[0] := by
  simp_rw [getLast, reverse_toList, getLast_reverse, toList_head]

@[simp]
lemma reverse_getPenult (F : M.Fan b c) : F.reverse.getPenult = F[1] := by
  rw [← F.reverse_reverse, reverse_getElem_one, reverse_reverse]

lemma reverse_getElem (F : M.Fan b c) (hi : i < F.reverse.length) :
    F.reverse[i] = F[F.length - 1 - i] := by
  rw [← getElem_toList]
  simp

lemma getElem_eq_reverse_getElem (F : M.Fan b c) (hi : i < F.length) :
    F[i] = F.reverse[F.length - 1 - i] := by
  grind [reverse_getElem]

/-- Add a new element to the end of a fan. -/
def concat (F : M.Fan b c) (heF : e ∉ F) (hT : (M.bDual !c).IsTriangle {F.getPenult, F.getLast, e})
    (c' : Bool := !c) (hc' : c' = !c := by simp) : M.Fan b c' :=
  (F.reverse.cons (e := e) (by simpa) (by simpa using hT.reverse) c' hc').reverse

lemma concat_toList (F : M.Fan b c) (heF : e ∉ F) {c'} {hc' : c' = !c} (hT) :
    (F.concat heF hT c' hc').toList = F.toList ++ [e] := by
  simp [concat]

@[simp, grind! .]
lemma concat_length (F : M.Fan b c) {heF : e ∉ F} {hT} {c'} {hc'} :
    (F.concat heF hT (c' := c') hc').length = F.length + 1 := by
  simp [concat]

lemma concat_getElem_of_lt (F : M.Fan b c) {heF : e ∉ F} {c'} {hc' : c' = !c} {hT} {i}
    (hi : i < F.length) : (F.concat heF hT c' hc')[i] = F[i] := by
  simp_rw [← getElem_toList, concat_toList, getElem_append_left hi]

@[simp]
lemma concatEq_getElem_length (F : M.Fan b c) {heF : e ∉ F} {c'} {hc' : c' = !c} {hT} :
    (F.concat heF hT c' hc')[F.length] = e := by
  simp [← getElem_toList, concat_toList]

/-- A fan gives a fan in any dual. -/
@[simps!]
def bDual (F : M.Fan b c) (d : Bool) (b' : Bool := (b != d)) (c' : Bool := (c != d))
    (hb' : b' = (b != d) := by simp) (hc' : c' = (c != d) := by simp) :
    (M.bDual d).Fan b' c' where
  toList := F
  toList_nodup := F.nodup
  toList_length_ge := F.length_ge_two
  toList_length_bodd := by simp [hb', hc', F.length_bodd]
  isNonloop' i hi d' := by simpa using F.isNonloop_bDual
  isTriangle' i hi := by cases d with simpa [hb', hc'] using! F.isTriangle i hi

/-- A fan of any dual gives a fan -/
@[simps!]
def ofbDual (b' : Bool := (b != d)) (c' : Bool := (c != d))
    (hb : b' = (b != d) := by simp) (hc : c' = (c != d) := by simp)
    (F : (M.bDual d).Fan b c) : M.Fan b' c' :=
  (F.bDual d b' c' hb hc).copy _ _ _ (by simp) (by simp) (by simp)

@[simp]
lemma bDual_length (F : M.Fan b c) (d : Bool) {b' c' hb hc} :
    (F.bDual d b' c' hb hc).length = F.length := rfl

@[simp]
lemma bDual_toSet (F : M.Fan b c) (d : Bool) {b' c' hb hc} :
    (F.bDual d b' c' hb hc : Set α) = F := rfl

@[simp]
lemma bDual_getElem (F : M.Fan b c) (d : Bool) {b' c' hb hc} (i : ℕ)
    (hi : i < (F.bDual d b' c' hb hc).length) :
    (F.bDual d)[i] = F[i] := rfl

@[simp]
lemma mem_bDual (F : M.Fan b c) (d : Bool) {b' c' hb hc} :
    x ∈ F.bDual d b' c' hb hc ↔ x ∈ F := Iff.rfl

lemma bDual_cons (F : M.Fan b c) (d : Bool) {b' c' b'' c'' hb hc hb'} {e : α}
     {he hT} :
    (F.cons (e := e) he hT b'' hb').bDual d b' c' hb hc =
      (F.bDual d b' c' (by _) hc).cons (e := e) (by
      simp [hb]
    ) hc := sorry
    -- (F.bDual d b' c' hb hc).cons (e := e) he hT =

def dual (F : M.Fan b c) (b' : Bool := !b) (c' : Bool := !c)
    (hb : b' = !b := by simp) (hc : c' = !c := by simp) : (M✶.Fan b' c') :=
  (F.bDual true).copy _ _ _ rfl (by simp [hb]) (by simp [hc])

@[reducible]
def ofDual (F : M✶.Fan b c) (b' : Bool := !b) (c' : Bool := !c)
    (hb : b' = !b := by simp) (hc : c' = !c := by simp) : (M.Fan b' c') :=
  (F.bDual true).copy _ _ _ (by simp) (by simp [hb]) (by simp [hc])

@[simp]
lemma bDual_false (F : M.Fan b c) {b' c' hb' hc'} :
    (F.bDual false b' c' hb' hc') = F.copy _ _ _ rfl (by simp [hb']) (by simp [hc']) := rfl

@[simp]
lemma bDual_true (F : M.Fan b c) {b' c' hb' hc'} :
    (F.bDual true b' c' hb' hc') = F.dual.copy _ _ _ rfl (by simp [hb']) (by simp [hc']) := rfl

/-- The length-2 fan given by a pair of non-loop, non-coloop elements. -/
@[simps]
def ofPair (he : ∀ i, (M.bDual i).IsNonloop e) (hf : ∀ i, (M.bDual i).IsNonloop f) (hef : e ≠ f)
    (b : Bool) (c : Bool := !b) (hbc : (!b) = c := by simp) : M.Fan b c where
  toList := [e, f]
  toList_nodup := by simpa
  toList_length_ge := by simp
  toList_length_bodd := by simp [← hbc]
  isNonloop' := by grind [Nat.le_one_iff_eq_zero_or_eq_one]
  isTriangle' := by simp

@[simp]
lemma toSet_ofPair (he : ∀ i, (M.bDual i).IsNonloop e) (hf : ∀ i, (M.bDual i).IsNonloop f)
    (hef : e ≠ f) {b c : Bool} (hbc : (!b) = c) :
      (Fan.ofPair he hf hef b c hbc : Set α) = {e, f} := by
  subst hbc
  rw [← ofPred_mem_toList_eq, ofPair_toList]
  simp [ofPred_or, pair_comm]

@[simp]
lemma length_ofPair (he : ∀ i, (M.bDual i).IsNonloop e) (hf : ∀ i, (M.bDual i).IsNonloop f)
    (hef : e ≠ f) (b c : Bool) (hbc) : (Fan.ofPair he hf hef b c hbc).length = 2 := rfl

lemma getElem_ofPair {he : ∀ i, (M.bDual i).IsNonloop e} {hf} {hef : e ≠ f} {b c hbc}
    {hi : i < (ofPair he hf hef b c hbc).length} :
    (ofPair he hf hef b c hbc)[i] = if i = 0 then e else f := by
  change [e,f][i] = _
  grind

@[simp]
lemma reverse_ofPair' (he : ∀ d, (M.bDual d).IsNonloop e) (hf : ∀ d, (M.bDual d).IsNonloop f)
    (hef : e ≠ f) {hbc : (!b) = c} : (ofPair he hf hef b c hbc).reverse =
      (ofPair hf he hef.symm c b (by simp [hbc])) :=
  Fan.toList_inj <| by simp [reverse_toList, ofPair_toList]

@[simp]
lemma cons_reverse (F : M.Fan b c) (heF : e ∉ F) (hT) (b' hb') :
    (F.cons heF hT b' hb').reverse =
      F.reverse.concat (by simpa) (by simpa using hT.reverse) b' hb' := by
  apply toList_inj
  simp_rw [reverse_toList, cons_toList, concat_toList, reverse_cons, reverse_toList]

lemma concat_reverse (F : M.Fan b c) (heF : e ∉ F) (hT) {c'} (hc : c' = !c) :
    (F.concat heF hT c' hc).reverse =
    F.reverse.cons (by simpa) (by simpa using hT.reverse) c' hc :=
  reverse_inj <| by simp

lemma eq_of_length_le_two (hF : F.length ≤ 2) : ∃ (e f : α) (he : ∀ i, (M.bDual i).IsNonloop e)
    (hf : ∀ i, (M.bDual i).IsNonloop f) (hef : e ≠ f) (hbc : (!b) = c),
    F = Fan.ofPair he hf hef b c hbc := by
  replace hF := hF.antisymm F.length_ge_two
  refine ⟨F[0], F[1], fun _ ↦ F.isNonloop_bDual, fun _ ↦ F.isNonloop_bDual, (by simp),
    by simpa [hF] using F.bool_left_eq, Fan.ext (by simpa) ?_⟩
  simp only [hF, Order.lt_two_iff, getElem_ofPair]
  grind

/-- The length-3 fan given by a triangle. -/
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

/-- The length-3 fan given by a triangle in some dual. -/
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

/-- Remove the element at the start of a fan. -/
@[simps]
def tail {b c} (F : M.Fan b c) (hF : 3 ≤ F.length) (b' : Bool := !b) (hb' : b' = !b := by simp) :
    M.Fan b' c where
  toList := (F : List α).tail
  toList_nodup := F.nodup.tail
  toList_length_ge := by grind
  toList_length_bodd := by
    subst hb'
    simp only [length_tail, length_toList, F.length_sub_one_bodd_eq]
    cases b with cases c with simp
  isNonloop' i hi d := by simpa using F.isNonloop_bDual (i := i + 1) (d := d)
  isTriangle' i hi := by simpa [hb'] using F.isTriangle (i := i + 1) (by grind)

@[simp, grind =]
lemma length_tail_add_one (F : M.Fan b c) (hF : 3 ≤ F.length) {b' : Bool} {hb' : b' = !b} :
    (F.tail hF b' hb').length + 1 = F.length :=
  List.length_tail_add_one _ <| by grind

@[simp, grind! .]
lemma length_tail_add_one' (F : M.Fan b c) (hF : 3 ≤ F.length) :
    (F.tail hF).length + 1 = F.length :=
  List.length_tail_add_one _ <| by grind

@[simp]
lemma getElem_tail (F : M.Fan b c) (hF : 3 ≤ F.length) {b' hb'}
    (hi : i < (F.tail hF b' hb').length) :
    (F.tail hF b' hb')[i] = F[i + 1]' (show i + 1 < F.length
      by rwa [← add_lt_add_iff_right (a := 1), length_tail_add_one] at hi) :=
  List.getElem_tail _

@[simp]
lemma getElem_mem_tail_iff (F : M.Fan b c) (hF : 3 ≤ F.length) (hi : i < F.length) {b' hb'} :
    F[i] ∈ F.tail hF b' hb' ↔ i ≠ 0 := by
  subst b'
  obtain rfl | i := i
  · exact iff_of_false (fun h0t ↦ by simpa using (F.tail hF).getElem_of_mem h0t) (by simp)
  rw [← F.getElem_tail hF _]
  · simpa using getElem_mem
  grind

lemma eq_tail_cons (F : M.Fan b c) (hF : 3 ≤ F.length) :
    F = (F.tail hF).cons (e := F[0]) (by simp) (by simpa using F.isTriangle 0 (by lia)) b
    (by simp) :=
  Fan.ext (by simp) (fun i hi hi' ↦ by cases i with simp)

lemma eq_cons_tail (F : M.Fan b c) (he : e ∉ F) (hT : (M.bDual !b).IsTriangle {e, F[0], F[1]})
    {b' hb'} : F = (F.cons he hT b' hb').tail
      (by grw [cons_length, ← F.length_ge_two]) b (by simp [hb']) := by
  refine Fan.ext ?_ fun i hi hi' ↦ by simp
  rw [← add_left_inj (a := 1), length_tail_add_one, cons_length]

@[simp]
lemma cons_tail_eq_copy (F : M.Fan b c) (he : e ∉ F)
    (hT : (M.bDual !b).IsTriangle {e, F[0], F[1]}) {b' b''} (hb : b' = !b) (hb'' : b'' = !b'):
    (F.cons he hT b' hb).tail (by grw [cons_length, ← F.length_ge_two]) b'' hb'' =
    F.copy M b'' c rfl (by rw [hb'', hb, b.not_not]) rfl := by
  refine Fan.ext ?_ fun i hi hi' ↦ ?_
  · rw [← add_left_inj (a := 1), length_tail_add_one, cons_length, copy_length]
  simp

/-- Remove the element at the end of a fan. -/
def dropLast (F : M.Fan b c) (hF : 3 ≤ F.length) (c' : Bool := !c) (hc : c' = !c := by simp) :
    M.Fan b c' :=
  (F.reverse.tail (by simpa) c' hc).reverse

@[simp]
lemma dropLast_toList (F : M.Fan b c) (hF : 3 ≤ F.length) {c' hc} :
    (F.dropLast hF c' hc : List α) = (F : List α).dropLast := by
  simp [dropLast]

lemma tail_reverse (F : M.Fan b c) (hF : 3 ≤ F.length) {b' hb'}:
    (F.tail hF b' hb').reverse = F.reverse.dropLast (by simpa) b' hb' := by
  simp [dropLast]

lemma dropLast_reverse (F : M.Fan b c) (hF : 3 ≤ F.length) {c' hc'} :
    (F.dropLast hF c' hc').reverse = F.reverse.tail (by simpa) c' hc' := by
  rw [dropLast, reverse_reverse]

@[simp, grind =]
lemma length_dropLast_add_one (F : M.Fan b c) (hF : 3 ≤ F.length) {c' : Bool} {hc' : c' = !c} :
    (F.dropLast hF c' hc').length + 1 = F.length := by
  simp [dropLast]

@[simp, grind! .]
lemma length_dropLast_add_one' (F : M.Fan b c) (hF : 3 ≤ F.length) :
    (F.dropLast hF).length + 1 = F.length := by
  simp [dropLast]

@[simp]
lemma getElem_dropLast (F : M.Fan b c) (hF : 3 ≤ F.length) {c' hc'}
    (hi : i < (F.dropLast hF c' hc').length) : (F.dropLast hF c' hc')[i] = F[i] := by
  rw! [← getElem_toList, dropLast_toList, List.getElem_dropLast, getElem_toList]
  rfl

@[simp]
lemma getElem_mem_dropLast_iff (F : M.Fan b c) (hF : 3 ≤ F.length) (hi : i < F.length)
    {c' hc'} : F[i] ∈ F.dropLast hF c' hc' ↔ i + 1 < F.length := by
  rw [dropLast, getElem_eq_reverse_getElem, mem_reverse, getElem_mem_tail_iff, ne_eq,
    Nat.sub_sub, Nat.sub_eq_zero_iff_le, not_le, add_comm]

lemma eq_dropLast_concat (F : M.Fan b c) (hF : 3 ≤ F.length) :
    F = (F.tail hF).cons (e := F[0]) (by simp) (by simpa using F.isTriangle 0 (by lia)) b
    (by simp) :=
  Fan.ext (by simp) (fun i hi hi' ↦ by cases i with simp)

lemma concat_dropLast_eq_copy (F : M.Fan b c) (he : e ∉ F) (hT ) {c' c''} (hc' : c' = !c)
    (hc'' : c'' = !c'):
    (F.concat he hT c' hc').dropLast (by grw [concat_length, ← F.length_ge_two]) c'' hc'' =
    F.copy M b _ rfl rfl (by rw [hc'', hc', Bool.not_not]) := by
  refine Fan.ext ?_ fun i hi hi' ↦ ?_
  · rw [← add_left_inj (a := 1), length_dropLast_add_one, concat_length, copy_length]
  simp only [getElem_dropLast, concat_getElem_of_lt _ (by simpa using hi'), copy_getElem]
  rfl

lemma eq_concat_dropLast (F : M.Fan b c) (he : e ∉ F) (hT)
    {c' hc'} : (F.concat he hT c' hc').dropLast
      (by grw [concat_length, ← F.length_ge_two]) c (by simp [hc']) = F := by
  simp [concat_dropLast_eq_copy]

@[elab_as_elim]
protected lemma induction {motive : ∀ {M : Matroid α} {b c : Bool} (_F : M.Fan b c), Prop}
    (pair : ∀ e f b (he : ∀ d : Bool, (M.bDual d).IsNonloop e)
      (hf : ∀ d : Bool, (M.bDual d).IsNonloop f) (hef : e ≠ f), motive (Fan.ofPair he hf hef b))
    (cons : ∀ b c (F₀ : M.Fan b c) (e : α) (heF₀ : e ∉ F₀)
      (hT : (M.bDual (!b)).IsTriangle {e, F₀[0], F₀[1]}) (_ih : motive F₀),
      motive (F₀.cons heF₀ (by simpa using hT))) (F : M.Fan b c) : motive F := by
  induction hi : F.length using Nat.strong_induction_on generalizing F b with | h n ih =>
  subst n
  obtain h2 | h3 := F.length_ge_two.eq_or_lt
  · obtain ⟨e, f, he, hf, hef, rfl, rfl⟩ := F.eq_of_length_le_two h2.ge
    apply pair
  have hwin := cons _ _ (F.tail (by lia)) F[0] (by simp) (by simpa using F.isTriangle 0 (by lia))
    <| ih _ (by grind) _ rfl
  rw [F.eq_tail_cons (by lia)]
  cases b with assumption

-- lemma joints_reverse (F : M.Fan b c) (d : Bool) : (F.joints d).reverse = F.reverse.joints d := by
--   _



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
