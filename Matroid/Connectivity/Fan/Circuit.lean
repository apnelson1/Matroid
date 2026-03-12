import Matroid.Connectivity.Fan.Basic
import Matroid.Connectivity.Triangle
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

lemma List.altBetween_eq_empty_of_ge (hji : j ≤ i) : L.altBetween i j b = ∅ := by
  grind [List.altBetween]

lemma altBetween_mono {p q p' q'} (L : List α) (hpp' : p ≤ p') (hqq' : q' ≤ q) (b : Bool) :
    L.altBetween p' q' b ⊆ L.altBetween p q b := by
  grind [altBetween]

lemma altBetween_eq_of_length_le (L : List α) (hj : L.length ≤ j) :
    L.altBetween i j b = L.altBetween i L.length b := by
  refine subset_antisymm ?_ (altBetween_mono _ rfl.le hj _)
  rintro e ⟨x, hx, hix, hxj, rfl, rfl⟩
  use x, hx, hix, hx

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

@[simp]
lemma altBetween_cons_false (L : List α) (q : ℕ) :
    (e :: L).altBetween 0 (q + 1) false = insert e (L.altBetween 0 q true) := by
  simp only [altBetween, zero_le, Order.lt_add_one_iff, true_and, length_cons, exists_and_left,
    Set.ext_iff, mem_setOf_eq, Set.mem_insert_iff]
  refine fun x ↦ ⟨?_, ?_⟩
  · rintro ⟨rfl | i, hiq, hi, hiL, rfl⟩
    · simp
    exact .inr ⟨i, by lia, by simpa using hi, hiL, rfl⟩
  rintro (rfl | ⟨i, hiq, hi, hiL, rfl⟩)
  · use 0
    simp
  exact ⟨i + 1, by lia, by simpa using hi, by lia, by simp⟩

@[simp]
lemma altBetween_cons_true (L : List α) (q : ℕ) :
    (e :: L).altBetween 0 (q + 1) true = L.altBetween 0 q false := by
  simp only [altBetween, zero_le, Order.lt_add_one_iff, true_and, length_cons, exists_and_left]
  simp only [Set.ext_iff, mem_setOf_eq, iff_def, forall_exists_index, and_imp]
  refine fun x ↦ ⟨?_, ?_⟩
  · rintro (rfl | i) hiq hi hiL rfl
    · simp at hi
    exact ⟨i, by lia, by simpa using hi, by grind⟩
  rintro i hiq hi hiL rfl
  exact ⟨i + 1, by lia, by simpa, by grind⟩

@[simp]
lemma altBetween_cons (L : List α) (q : ℕ) :
    (e :: L).altBetween (p + 1) (q + 1) b = L.altBetween p q (!b) := by
  refine subset_antisymm ?_ ?_
  · rintro _ ⟨rfl | i, hi, hpi, hiq, rfl, rfl⟩
    · lia
    simp only [Nat.bodd_succ, Bool.not_not, getElem_cons_succ]
    use i; grind
  rintro _ ⟨i, hi, hpi, hiq, hi', rfl⟩
  exact ⟨i + 1, by grind [Nat.bodd_succ, length_cons]⟩

namespace Matroid


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

lemma IsFan.extract_subset_closure_altBetween (hF : M.IsFan F b c) (hi : i.bodd = b)
    (hj : j.bodd = !b) (hjF : j < F.length + 1) :
    {x | x ∈ F.extract i j} ⊆ M.closure (F.altBetween i j b) := by
  obtain rfl | j := j; simp
  simp_rw [Set.subset_def, mem_extract_iff_getElem]
  simp only [exists_and_left, mem_setOf_eq, forall_exists_index, and_imp]
  rintro e x hix hxj hlt rfl
  obtain rfl | rfl := b.eq_or_eq_not x.bodd
  · refine mem_closure_of_mem' _ ?_ (by grind)
    simp [hF.nodup.getElem_mem_altBetween_iff, hix, hxj]
  grw [← hF.altBetween_subset_closure_altBetween hi (by simpa using hj) (by lia), Bool.not_not,
    hF.nodup.getElem_mem_altBetween_iff]
  simp [hix, hxj]

-- lemma IsFan.foo (hF : M.IsFan F true c) (hij : i ≤ j) {hj : j < F.length}
--     (h0 : M.IsTriangle {F[0], F[i], F[j]}) : (i = 1 ∧ j + 1 = F.length) ∨ F.length = 4 := by
--   -- by_contra!
--   obtain rfl | hne := eq_or_ne i j; simp at h0
--   obtain rfl | i := i; simp at h0
--   obtain rfl | rfl | j := j; lia; lia

--   have h01 := hF.mem_or_mem₁₂ 0 _ (by lia) h0.isCircuit (by simp)
--   replace h01 : i = 0 ∨ i = 1 ∨ j = 0 := by simpa [hF.nodup.getElem_inj_iff] using h01
--   replace h01 := show i = 0 ∨ i = 1 by lia
--   by_cases hjb : j.bodd
--   · by_cases hjF : F.length = j + 3
--     · obtain rfl | rfl := h01; lia
--       obtain rfl | rfl | rfl | j := j; simp at hne; simpa; simp at hjb
--       have h2 := hF.mem_or_mem₁₂ 2 {F[0], F[2], F[j + 5]} (by lia) h0.isCircuit (by simp)
--       simp [hF.nodup.getElem_inj_iff] at h2
--     have h1 := hF.mem_or_mem₀₂ (j + 1) {F[0], F[i + 1], F[j + 1 + 1]} (by lia)
--       (by simpa [hjb] using h0.isCircuit) (by simp)
--     replace h1 : j = i ∨ j + 2 = i := by simpa [hF.nodup.getElem_inj_iff] using h1
--     obtain rfl | i := i; sorry
--     have hodd : i.bodd = false := sorry
--     have h3 := hF.mem_or_mem₀₁ i {F[0], F[i + 2], F[j + 2]} (by lia)
--       (by simpa [hodd] using h0.isCircuit) (by simp)
--     replace h3 : (i = 0 ∨ i = j + 2) ∨ i = j + 1 := by simpa [hF.nodup.getElem_inj_iff] using h3
--     obtain rfl : j = i + 1 := by lia
--     obtain rfl : i = 0 := by lia
--     simp

--   simp only [Bool.not_eq_true] at hjb
--   have hw4 := hF.mem_or_mem₀₁ j {F[0], F[i + 1], F[j + 2]} (by lia)
--     (by simpa [hjb] using h0.isCircuit) (by simp)
--   replace hw4 : (j = 0 ∨ j = i + 1) ∨ j = i := by simpa [hF.nodup.getElem_inj_iff] using hw4

--   obtain rfl | rfl := h01
--   · obtain rfl | rfl : j = 1 ∨ j = 0 := by lia
--     · contradiction
--     by_contra! hcon
--     have hwin := hF.mem_or_mem₁₂ 2 {F[0], F[1], F[2]} (by lia) h0.isCircuit (by simp)
--     simp [hF.nodup.getElem_inj_iff] at hwin
--   obtain rfl : j = 2 := by grind
--   simp
--   sorry

  -- · simp








    -- obtain rfl | i := i
    -- ·
  -- obtain rfl | rfl | rfl | i := i
  -- · simp at h0
  -- · by_contra! hcon
  --   obtain rfl | rfl | rfl | j := j; lia; lia
  --   · have hwin := hF.mem_or_mem₁₂ 2 _ (by lia) h0.isCircuit (by simp)
  --     grind [hF.nodup.getElem_inj_iff]
  --   by_cases hjb : j.bodd
  --   · have := hF.mem_or_mem₀₁ (j + 1) {F[0], F[0 + 1], F[j + 3]} (by lia)
  --       (by simpa [hjb] using h0.isCircuit) (by simp)
  --     grind [hF.nodup.getElem_inj_iff]
  --   obtain hlt | heq := (show j + 4 ≤ F.length from hj).lt_or_eq
  --   · have hwin := hF.mem_or_mem₀₂ (i := j + 2) (C := {F[0], F[0 + 1], F[j + 3]}) (by lia)
  --       (by simpa [hjb] using h0.isCircuit)
  --     simp [hF.nodup.getElem_inj_iff] at hwin
  --   grind
  -- · sorry
  -- have := hF.mem_or_mem₁₂ 0 _ (by lia) h0.isCircuit
  -- grind [hF.nodup.getElem_inj_iff]


  -- have h1 := hF.mem_or_mem₁₂ (i := 0) (C := {F[0], F[i + 3], F[j]})
  --   (by lia) h0.isCircuit (by simp)
  -- simp [hF.nodup.getElem_inj_iff, show 1 ≠ j by lia, show 2 ≠ j by lia] at h1

  -- -- simp [hF.nodup.getElem_inj_iff, add_right_comm, or_right_comm] at h1
  -- have h1 := hF.mem_or_mem₁₂ (i := 0) (C := {F[0], F[i + 1], F[j]}) (by lia) h0.isCircuit (by simp)
  -- obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ 2 = j := by
  --   simpa [hF.nodup.getElem_inj_iff, show 1 ≠ j by lia] using h1


  -- obtain h_eq | hlt := h4.eq_or_lt'
  -- · assumption
  -- have := hF.mem_iff_mem₀₁ (i := 2) (C := {F[0], F[1], F[3]}) (by lia) (by simpa using h0.isCircuit)
  -- simp at this
  -- have := hF.isTriad_getElem_of_eq 2 (by lia) rfl

-- inductive IsClosedFan (M : Matroid α) : List α → Bool → Bool → Prop
--   | of_parallel (F b) (hF : M.IsFan F b b) (h : (M.bDual b).Parallel F[0] F[F.length - 1]) :
--       M.IsClosedFan F b b
--   | of_triangle (F b) (hF : M.IsFan F b (!b))
--       (h : (M.bDual b).IsTriangle {F[F.length - 1], F[F.length - 2], F[0]}) : M.IsClosedFan F b (!b)

-- @[grind →]
-- lemma IsClosedFan.isFan (h : M.IsClosedFan F b c) : M.IsFan F b c := by
--   cases h with assumption

-- lemma IsFan.isClosedFan_of_parallel (hF : M.IsFan F b b)
--     (h : (M.bDual b).Parallel F[0] F[F.length - 1]) : M.IsClosedFan F b b :=
--   IsClosedFan.of_parallel _ _ hF h

-- lemma IsFan.isClosedFan_of_triangle (hF : M.IsFan F b (!b))
--     (h : (M.bDual b).IsTriangle {F[F.length - 1], F[F.length - 2], F[0]}) :
--     M.IsClosedFan F b (!b) :=
--   IsClosedFan.of_triangle _ _ hF h

-- lemma IsFan.isClosedFan_of_triangle_not (hF : M.IsFan F (!b) b)
--     (h : (M.bDual (!b)).IsTriangle {F[F.length - 1], F[F.length - 2], F[0]}) :
--     M.IsClosedFan F (!b) b := by
--   nth_rw 2 [← b.not_not] at hF
--   simpa using hF.isClosedFan_of_triangle (by simpa)

-- lemma IsClosedFan.parallel_bDual (h : M.IsClosedFan F b b) :
--     (M.bDual b).Parallel F[0] F[F.length - 1] := by
--   cases b with cases h with assumption

-- lemma IsClosedFan.isTriangle_bDual (h : M.IsClosedFan F b (!b)) :
--     (M.bDual b).IsTriangle {F[F.length - 1], F[F.length - 2], F[0]} := by
--   cases b with cases h with assumption

-- lemma isClosedFan_iff_self :
--     M.IsClosedFan F b b ↔ ∃ (h : M.IsFan F b b), (M.bDual b).Parallel F[0] F[F.length - 1] := by
--   grind [IsClosedFan]

-- lemma isClosedFan_iff_not : M.IsClosedFan F b (!b) ↔
--     ∃ (h : M.IsFan F b (!b)), (M.bDual b).IsTriangle {F[F.length - 1], F[F.length - 2], F[0]} := by
--   grind [IsClosedFan]

-- lemma isClosedFan_not_iff : M.IsClosedFan F (!b) b ↔ ∃ (h : M.IsFan F (!b) b),
--     (M.bDual (!b)).IsTriangle {F[F.length - 1], F[F.length - 2], F[0]} := by
--   simpa using isClosedFan_iff_not (b := !b)

/-- The joints are always independent, unless the first and last element are parallel joints. -/
lemma IsFan.joints_indep (hF : M.IsFan F b c)
    (h_pair : b = false → c = false → ¬ M.Parallel F[0] F[F.length - 1]) :
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
  refine h_pair rfl rfl <| ?_
  rw [parallel_iff_isCircuit (by grind)]
  simpa [hn, ← h_eq]

lemma IsFan.joints_indep' (hF : M.IsFan F b c)
    (h_pair : b = false → c = false → ¬ M.Parallel F[0] F[F.length - 1]) :
    M.Indep (F.get '' {i | i.1.bodd = b}) := by
  convert hF.joints_indep h_pair
  refine Set.ext fun i ↦ ?_
  simp only [get_eq_getElem, mem_image, mem_setOf_eq, and_comm (a := _ = b)]
  constructor
  · rintro ⟨⟨x ,hx⟩, rfl, rfl⟩; grind
  rintro ⟨i, hi, rfl, rfl⟩
  use ⟨i, hi⟩

lemma IsFan.joints_indep'' (hF : M.IsFan F b c)
    (h_pair : b = false → c = false → ¬ M.Parallel F[0] F[F.length - 1]) :
    M.Indep (F.altBetween 0 F.length b) := by
  convert hF.joints_indep h_pair
  grind [subset_antisymm_iff, altBetween]

lemma IsFan.joints_tail_indep (hF : M.IsFan F b c) :
    M.Indep (F.tail.altBetween 0 F.tail.length (!b)) := by
  obtain rfl | rfl := b
  · obtain h2 | h3 := hF.two_le_length.eq_or_lt'
    · obtain ⟨e, f, rfl⟩ := length_eq_two.1 h2
      simp only [tail_cons, length_cons, length_nil, zero_add]
      exact (hF.isNonloop (e := f) (by simp)).indep.subset <|
        (altBetween_subset ..).trans <| by simp
    exact (hF.tail (by lia)).joints_indep'' (by simp)
  refine (hF.joints_indep'' (by simp)).subset ?_
  cases F with simp

lemma IsFan.joints_dropLast_indep (hF : M.IsFan F b c) :
    M.Indep (F.dropLast.altBetween 0 F.dropLast.length b) := by
  obtain rfl | rfl := c
  · obtain h2 | h3 := hF.two_le_length.eq_or_lt'
    · obtain ⟨e, f, rfl⟩ := length_eq_two.1 h2
      simp only [dropLast_cons₂, dropLast_singleton, length_cons, length_nil, zero_add]
      exact (hF.isNonloop (e := e) (by simp)).indep.subset <|
        (altBetween_subset ..).trans <| by simp
    exact (hF.dropLast (by lia)).joints_indep'' (by simp)
  refine (hF.joints_indep'' (by simp)).subset ?_
  cases F using List.reverseRecOn with grind [altBetween]

lemma IsFan.altBetween_indep (hF : M.IsFan F b c)
    (hij : b = false → c = false → i = 0 → F.length ≤ j + 1 → ¬ M.Parallel F[0] F[F.length - 1]) :
    M.Indep (F.altBetween i (j + 1) b) := by
  wlog hj : j + 1 ≤ F.length generalizing j with aux
  · rw [altBetween_eq_of_length_le _ (by lia),
      show F.length = (F.length - 1) + 1 by grind [hF.two_le_length]]
    exact aux (by grind) <| by grind
  wlog hijle : i ≤ j generalizing i with aux
  · rw [altBetween_eq_empty_of_ge (by lia)]
    simp
  obtain rfl | i := i
  · obtain heq | hlt := hj.eq_or_lt
    · exact (hF.joints_indep'' (by grind)).subset <| altBetween_mono _ rfl.le hj _
    exact hF.joints_dropLast_indep.subset <| by grind [altBetween]
  refine hF.joints_tail_indep.subset ?_
  cases F with
  | nil => simp [altBetween]
  | cons e F =>
    simp only [altBetween_cons, tail_cons]
    exact altBetween_mono _ (by lia) (by grind) _

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
    have hsk := (hF.joints_indep'' (by simpa using h_pair)).subset_skew_diff (J := {e})
      (by grind [altBetween])
    refine hsk.closure_skew_right.mono_right ?_
    simp only [length_cons, altBetween_cons_false]
    grw [insert_diff_self_of_notMem (by grind [altBetween_subset, hF.nodup]),
      ← altBetween_mono _ (p' := i) (q' := i + 3) (by lia) (by lia),
      ← hF'.extract_subset_closure_altBetween (by simpa) (by simpa) (by lia)]
    grind [insert_subset_iff, hF'.nodup.getElem_mem_extract_iff]

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
      simp only [bDual_false, contract_isNonloop_iff, mem_diff]
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


-- lemma IsFan.contract_head' (hF : M.IsFan F true c) (h4 : 4 ≤ F.length)
--     (h01 : ¬ M.Parallel F[0] F[1]) : (M ／ {F[0]}).IsFan F.tail false c := by
--   obtain h4 | h5 := h4.eq_or_lt
--   · sorry
--   refine (hF.tail (by lia)).contract_disjoint (by grind) ?_ ?_ ?_




/-- Let `F[i]` and `F[j]` be joints of a fan, and `K` be the set of cojoints between `i` and `j`.
If `F[i]` and `F[j]` are not parallel and at the beginning and the end of the fan,
then `{F[i], F[j]} ∪ K` is a circuit.

The nondegeracy hypothesis has some redundancy, since `i = 0` and `j + 1 = F.length` implies that
`b = c = false`; we include it so it is easier to discharge quickly in various cases.  -/
lemma IsFan.isCircuit_interval (hF : M.IsFan F b c) (hij : i < j) (hjF : j < F.length)
    (hib : i.bodd = b) (hjb : j.bodd = b)
    (hp : b = false → c = false → i = 0 → j + 1 = F.length → ¬ M.Parallel F[0] F[F.length - 1]) :
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
    specialize ih (by lia) (by lia) (by simp [Nat.bodd_two]) (by grind)
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
    have hcl : (insert F[i] (insert F[i + 2 * d + 2] (F.altBetween i (i + 2 * d + 2) !i.bodd)))
        ⊆ M.closure (F.altBetween i (i + 2 * d + 2 + 1) i.bodd) := by
      grw [← hF.extract_subset_closure_altBetween rfl (by simp) (by lia),
        insert_subset_iff, insert_subset_iff, altBetween_subset_iff]
      simp_rw [mem_setOf, hF.nodup.getElem_mem_extract_iff]
      grind
    grw [← eLocalConn_closure_right, insert_comm (a := F[i + 2 * d + 2]),
      M.eLocalConn_mono_left hcl, closure_insert_eq_of_mem_closure, eLocalConn_closure_closure,
      Indep.eLocalConn_eq_encard_inter, encard_le_one_iff_subsingleton]
    · rw [inter_insert_of_mem]
      · simp [hF.nodup.getElem_mem_altBetween_iff]
      simp [hF.nodup.getElem_mem_altBetween_iff, add_assoc]
    · refine (hF.altBetween_indep (i := i) (j := i + 2 * d + 5) ?_).subset ?_
      · rintro - rfl rfl hl
        obtain h1 | h1 := hl.eq_or_lt
        · simpa [h1] using hF.length_bodd_eq
        grind
      refine union_subset (altBetween_mono _ (by lia) (by lia) _) ?_
      simp [insert_subset_iff, hF.nodup.getElem_mem_altBetween_iff, add_assoc]
    exact (hF.isTriangle_getElem_of_eq (i + 2 * d + 2) (by lia) (by simp)).mem_closure₂

/-- If a circuit of a matroid contains joints `F[i + 1], F[j]` of a fan `F`,
and does not contain the cojoint `F[i]`,
then it comprises precisely `F[i + 1], F[j]`, and the cojoints between them.  -/
lemma IsFan.eq_interval_of_notMem_mem_mem {i j : ℕ} (hF : M.IsFan F b c) (hij : i + 1 < j)
    (hjF : j < F.length) (hib : i.bodd = !b) (hj : j.bodd = b) (hC : M.IsCircuit C) (hiC : F[i] ∉ C)
    (hi1C : F[i + 1] ∈ C) (hjC : F[j] ∈ C) :
    C = insert F[i + 1] (insert F[j] (F.altBetween (i + 1) j (!b))) := by
  obtain ⟨j', hij', hj'j, hj'b, hj'C⟩ | hmin := exists_or_forall_not
      (fun j' ↦ ∃ (hij : i + 1 < j') (hj : j' < j) (hj'b : j'.bodd = b), F[j'] ∈ C)
  · rw [IsFan.eq_interval_of_notMem_mem_mem hF hij' (by lia) hib hj'b hC hiC hi1C hj'C] at hjC
    simp [hF.nodup.getElem_inj_iff, hF.nodup.getElem_mem_altBetween_iff, hj,
      hj'j.ne.symm, hij.ne.symm] at hjC
  simp only [exists_prop, exists_and_left, not_and, not_exists] at hmin
  have hC' := hF.isCircuit_interval hij hjF (by simpa) hj (by simp)
  refine hC.eq_of_superset_isCircuit hC' <| insert_subset hi1C <| insert_subset hjC ?_
  suffices aux : ∀ x (hix : i + 1 < x) (hxj : x < j) (hxb : x.bodd = !b), F[x] ∈ C by
    rw [← altBetween_add_one_left_eq_self (by simpa)]
    rintro _ ⟨x, hx, hix, hxj, hxb, rfl⟩
    refine aux _ (by lia) hxj hxb
  intro x hx hxj hxb
  induction x using Nat.twoStepInduction with
  | zero => simp at hx
  | one => simp at hx
  | more x ih0 _ =>
    simp at hxb
    obtain rfl | hne := eq_or_ne x i
    · have hwin := hF.mem_or_mem₀₂ x C (by lia) (by simpa [hib]) hi1C
      rwa [or_iff_right hiC] at hwin
    obtain rfl | hne := eq_or_ne x (i + 1)
    · simp [hib] at hxb
    rw [← hF.mem_iff_mem₀₂ _ _ (by lia) (by simpa [hxb])]
    · exact ih0 (by lia) (by lia) (by simpa using hxb)
    exact hmin _ (by lia) (by simpa) (by lia)
termination_by j

lemma IsFan.exists_eq_interval_of_notMem_mem_add_one {t : ℕ} (hF : M.IsFan F b c) (hit : i + 1 < t)
    (htF : t < F.length) (hib : i.bodd = !b) (hj : t.bodd = !b) (hC : M.IsCircuit C)
    (hiC : F[i] ∉ C) (hi1C : F[i + 1] ∈ C) (ht : F[t] ∉ C) :
    ∃ (j : ℕ) (hij : i + 1 < j) (hjt : j < t), j.bodd = b ∧
    C = insert F[i + 1] (insert F[j] (F.altBetween (i + 1) j (!b))) := by
  obtain hle | hlt := le_or_gt t (i + 3)
  · obtain rfl | rfl | rfl := show t = i + 1 ∨ t = i + 2 ∨ t = i + 3 by lia
    · simp [hib] at hj
    · grind [hF.mem_or_mem₀₂ i C (by lia) (by simpa [hib]) hi1C]
    simp [hib] at hj
  obtain ⟨t₀, ht₀⟩ := Nat.exists_eq_add_of_le' (show 2 ≤ t by lia)
  have ht₀b : t₀.bodd = !b := by simp [← hj, ht₀]
  by_cases ht₀C : F[t₀] ∈ C
  · rw [hF.mem_iff_mem₀₁ _ _ (by lia) (by simpa [ht₀b]) (by simpa [← ht₀])] at ht₀C
    obtain rfl := hF.eq_interval_of_notMem_mem_mem (i := i) (j := t₀ + 1) (C := C) (by lia) (by lia)
      hib (by simpa) hC hiC hi1C ht₀C
    exact ⟨t₀ + 1, by lia, by lia, by simpa, rfl⟩
  have hwin := IsFan.exists_eq_interval_of_notMem_mem_add_one hF (t := t₀) (by lia) (by lia)
    hib ht₀b hC hiC hi1C ht₀C
  grind
termination_by t

/-- If a circuit doesn't contain two cojoints of a fan, but it contains something between them,
then it is an interval. -/
lemma IsFan.exists_eq_interval_of_notMem_mem_notMem {s i t : ℕ} (hF : M.IsFan F b c) (hsi : s < i)
    (hit : i < t) (ht : t < F.length) (hsb : s.bodd = !b) (htb : t.bodd = !b)
    (hC : M.IsCircuit C) (hsC : F[s] ∉ C) (hiC : F[i] ∈ C) (htC : F[t] ∉ C) :
    ∃ (p q : ℕ) (_ : s < p) (hpq : p < q) (hq : q < t),
    p.bodd = b ∧ q.bodd = b ∧ C = insert F[p] (insert F[q] (F.altBetween p q (!b))) := by
  by_cases hs1 : F[s + 1] ∈ C
  · obtain ⟨j, hsj, hjt, rfl, rfl⟩ :=
      hF.exists_eq_interval_of_notMem_mem_add_one (by lia) ht hsb htb hC hsC hs1 htC
    exact ⟨s + 1, j, by simp [hsb, hsj, hjt]⟩
  have hs1i : s + 1 < i := by grind
  rw [hF.mem_iff_mem₁₂ _ _ (by lia) (by simpa [hsb]) hsC] at hs1
  have hlt : i - (s + 2) < i - s := by lia
  have hs2i : s + 2 < i := by grind
  have hwin := hF.exists_eq_interval_of_notMem_mem_notMem (s := s + 2) (i := i) (t := t) hs2i hit ht
    (by simpa) htb hC hs1 hiC htC
  grind
termination_by i - s

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
the second element of `C`, then `C` has a circuit containing the first element of `F`,
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
    have elim := hC₀'.strong_elimination hT.isCircuit (e := F[k + 2]) (f := F[0]) hkC (by simp) h0C₀'
      (by simp [hF.nodup.getElem_inj_iff])
    obtain ⟨C₀, hC₀ss, hC₀, h0C₀⟩ := elim
    refine ⟨C₀, hC₀, h0C₀, ?_, fun i hi hiC₀ ↦ by grind [hF.nodup.getElem_inj_iff]⟩
    grw [hC₀ss, hC₀'ss, diff_subset]
    grind [Set.union_subset_iff, insert_subset_iff]

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

lemma foo {M : Matroid α} {F : List α} (hF : M.IsFan F true false)
    (hT : M.IsTriad {F[F.length - 2], F[F.length - 1], F[0]})
    (hconn : (M ＼ {F[0]}).Connected) : M.IsTriangle {F[F.length - 1], F[0], F[1]} := by
  obtain ⟨n, hn⟩ : ∃ n, F.length = 2 * n + 4 := sorry
  simp only [hn, Nat.reduceSubDiff, Nat.add_one_sub_one] at hT ⊢
  have hF4 : 4 ≤ F.length := sorry

  have hE : M.E = {e | e ∈ F} := by
    refine hF.subset_ground.antisymm' fun x hx ↦ by_contra fun hfX ↦ ?_
    obtain ⟨C, hC, hxC, h1C⟩ := hconn.exists_isCircuit_of_ne (e := x) (f := F[1]) (by grind)
      (by grind [hF.nodup.getElem_inj_iff]) (by grind)
    simp only [delete_isCircuit_iff, disjoint_singleton_right] at hC
    by_cases h1 : F[2 * n + 3] ∈ C
    · have hC_eq := hF.eq_interval_of_notMem_mem_mem (by lia) (by lia)
        rfl (by simp) hC.1 (by grind) h1C h1
      simp only [hC_eq, zero_add, altBetween, exists_and_left, Set.mem_insert_iff] at hxC
      grind
    rw [hT.reverse.mem_iff_mem_of_isCocircuit (by simpa using hC.1) hC.2] at h1
    obtain ⟨j, _, _, _, rfl⟩ :=
      hF.exists_eq_interval_of_notMem_mem_add_one (i := 0) (t := 2 * n + 2) (C := C)
      (by lia) (by lia) rfl (by simp) hC.1 hC.2 h1C h1
    simp only [zero_add, altBetween, Bool.not_true, exists_and_left, Set.mem_insert_iff] at hxC
    grind
  have hnp : ¬M.Parallel F[1] F[2 * n + 3] := by
    intro hC
    simpa [hF.nodup.getElem_inj_iff] using hT.isCocircuit.mem_iff_mem_of_parallel hC
  rw [pair_comm, insert_comm, isTriangle_iff_parallel_contract hnp]
  by_contra hcon

  have := (hF.dual.contract_head (by lia) (by simp)).dual
  simp at this
  -- by_cases hpara : (M ／ {F[0]}).Parallel F[2 * n + 3] F[1]
  -- · rw [parallel_iff_isCircuit (by simp [hF.nodup.getElem_inj_iff])] at hpara

    -- rw [← hF.mem_iff_mem₁₂] at h1
    -- have := hF.exists_eq_interval_of_notMem_mem_add_one (i := 0) ()



/-- If `F = [a, b, ..., y, z]` is an even-length fan with `a` a joint,
and `y, z, a` is a triangle, then `z, a, b` is a triad, provided that `M ／ a` is connected.
This hypothesis is necessary, since otherwise a `2`-sum with guts `a` would give a problem. -/
lemma bar {M : Matroid α} {F : List α} (hF : M.IsFan F false true)
    (hT : M.IsTriangle {F[F.length - 2], F[F.length - 1], F[0]})
    (hconn : (M ／ {F[0]}).Connected) : M.IsTriad {F[F.length - 1], F[0], F[1]} := by
  have hE : M.E = {e | e ∈ F} := by
    refine hF.subset_ground.antisymm' fun x hx ↦ by_contra fun (hxF : x ∉ F) ↦ ?_
    have := hconn.to_dual.exists_isCircuit_of_ne (e := x) (f := F[1]) ?_ ?_
    sorry
    sorry
    sorry
  sorry
--   have hF4 : 4 ≤ F.length := by
--     by_contra! hcon
--     obtain hF2 | hF3 : F.length = 2 ∨ F.length = 3 := by grind [hF.two_le_length]
--     · simp [hF2] at hT
--     simpa [hF3] using hF.length_bodd_eq
--   obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le' hF4
--   obtain hd | hi := (M.indep_or_dep (X := {F[0], F[2], F[3]}) (by grind [hF.subset_ground])).symm
--   ·
--   obtain h4 | hlt := hF4.eq_or_lt
--   · simp only [h4.symm, Nat.reduceSub, Nat.add_one_sub_one, dual_isTriangle_iff] at hT ⊢
--     have hT1 : M.IsTriangle {F[0], F[1], F[2]} := hF.isTriangle_getElem_of_eq 0 (by lia) (by simp)
--     have hT2 : M.IsTriad {F[1], F[2], F[3]} := hF.isTriad_getElem_of_eq 1 (by lia) (by simp)
--     exact (hT.rotate.triad_of_isTriangle_isTriad hT1.swap_right hT2.rotate_left hconn).swap_left
--   set N := M ／ {F[0]} ＼ {F[1]} with hN
--   set F' := F.drop 2 with hF'
--   have hFN : N.IsFan F' false true := by
--     convert (hF.contract_head (by lia) (by simp)).delete_head (by grind) (fun _ hp ↦ ?_) using 1
--     · simpa
--     · simp [hF', ← drop_one]
--     replace hp : M✶.Parallel F[1] F[F.length - 1 - 1 + 1] := by
--       simpa [delete_parallel_iff, hF.nodup.getElem_inj_iff] using hp
--     have hwin := (hF.isTriangle_getElem_of_eq 0 (by lia) rfl).mem_iff_mem_of_isCocircuit
--       <| hp.isCircuit_of_ne ?_
--     · simp [hF.nodup.getElem_inj_iff, show F.length ≠ 3 by lia] at hwin
--     simp only [ne_eq, hF.nodup.getElem_inj_iff]
--     lia
--   have hlen : F'.length < F.length := by grind
--   have hT : N.IsTriangle {F'[F'.length - 2], F'[F'.length - 1], F'[0]} := by
--     suffices (M ／ {F[0]}).IsTriangle {F[n + 2], F[n + 3], F[2]} by
--       simpa [hN, isTriangle_delete_iff, hF', hF.nodup.getElem_inj_iff, hn, add_comm 2]
--     have := hF.joints_indep (by simp)
--     have := hT.swap_left.union_diff_singleton_isCircuit
--       (hF.isTriangle_getElem_of_eq 0 (by lia) (by simp)).reverse
--     simp [hF.nodup.getElem_inj_iff, hn] at this
--   have hconn : (N ／ {F'[0]}).Connected := by
--     rw [hN, ← contract_delete_comm _ (by grind [hF.nodup.getElem_inj_iff])]
--     refine hconn.contract_delete_connected_of_mem_triad_of_parallel
--       (T := {F'[0], F[1], F[0]}) ?_ ?_ ?_ ?_ ?_
--     · sorry
--     · sorry
--     · sorry
--     · sorry
--     sorry
--   have hT' := foo hFN hT hconn

-- termination_by F.length

  -- have hconn' : (((M ／ {F[0]} ＼ {F[1]})) ／ {(F.drop 2)[0]}).Connected := sorry
  -- have hT' : (((M ／ {F[0]} ＼ {F[1]}))
  -- induction n : F.length using Nat.twoStepInduction
  -- induction hF using IsFan.induction₂_even with
  -- | of_pair => simp at hT
  -- | cons_cons M e f x y F b h hT₁ hf hT₂ he hey ih =>
  --   simp_all only [length_cons, Nat.reduceSubDiff, add_tsub_cancel_right, getElem_cons_succ,
  --     getElem_cons_zero]
  --   have


-- lemma IsClosedFan.reverse (h : M.IsClosedFan F b c) : M.IsClosedFan F.reverse c b := by
--   cases h with
--   | of_parallel hF h => exact IsClosedFan.of_parallel _ _ hF.reverse <| by simpa using h.symm
--   | of_triangle hF h =>
--     suffices aux : (M.bDual !b).IsTriangle {F[0], F[1], F[F.length -1]} from
--       hF.reverse.isClosedFan_of_triangle_not <| by
--         simpa [show F.length - 1 - (F.length - 2) = 1 by grind]
--     have hn : 3 ≤ F.length := sorry

--     rw [isTriangle_iff, encard_insert_of_notMem (by grind [hF.nodup.getElem_inj_iff]),
--       encard_pair (by grind [hF.nodup.getElem_inj_iff]), and_iff_left (by norm_num)]
--     wlog hb : b = true generalizing b M F with aux
--     · obtain rfl : b = false := by grind
--       simpa using aux (M := M✶) (F := F) (b := true) (by simpa) (by simpa) hn rfl
--     obtain rfl := hb
--     simp_all only [bDual_true, dual_isTriangle_iff, Bool.not_true, bDual_false]

--     have h1 : (M ↾ {e | e ∈ F}).IsFan F true false := by
--       obtain h3 | h4 := hn.eq_or_lt
--       · simpa [← h3] using hF.length_bodd_eq
--       refine hF.minor h4 (restrict_isRestriction _ _ hF.subset_ground).isMinor rfl.subset ?_ ?_
--       · sorry
--       simp [hF.isNonloop]



--     have hnp : ¬ M✶.Parallel F[0] F[2] := fun hp ↦ by
--       rw [parallel_iff_isCircuit (by simp [hF.nodup.getElem_inj_iff])] at hp
--       have hcon := (hF.isTriad_getElem_of_eq 0 (by lia) rfl).isCircuit.eq_of_superset_isCircuit hp
--         (by grind)
--       apply_fun (F[1] ∈ ·) at hcon
--       simp [hF.nodup.getElem_inj_iff] at hcon



--     obtain ⟨C, hC, h0C, h2C⟩ := IsNonloop.exists_isCircuit_mem_notMem (M := M) (e := F[0])
--       (f := F[2]) (hF.dual.isNonloop (by simp)) hnp
--     have hT0 := (hF.isTriad_getElem_of_eq 0 (by lia) rfl).swap_right
--     have h1C : F[1] ∈ C := hT0.mem_of_mem_of_notMem_of_is_Cocircuit (by simpa) h0C h2C

--     obtain ⟨C₀, hC₀ss, hC₀, h0C₀⟩ :=
--       (hF.tail hn).exists_isCircuit_subset_first_last hC (by simpa) (by simpa)
--     simp at hC₀ss
--     -- have hCi (i) (hi : i + 2 < F.length) : F[i + 2] ∉ C := by
--     --   induction i with
--     --   | zero => assumption
--     --   | succ i ih =>

--     --     by_cases hib : i.bodd
--     --     · have := (hF.isTriad_getElem_of_eq (i + 1) (by lia) (by simpa))
--     --       rw [← this.mem_iff_mem_of_isCocircuit]
--     --       rw [← (hF.isTriad_getElem_of_eq (i + 1) (by lia) (by simpa)).mem_iff_mem_of_isCocircuit
--     --         (by simpa)]
--     --       · apply ih (by lia)
--     --       obtain rfl | i := i
--     --       · simp at hib
--     --       obtain rfl | i := i
--     --       · assumption







--     -- simp_all only [bDual_false, Bool.not_false, bDual_true]



--     isCircuit_iff_restr_eq_circuitOn (by simp) (by grind [hF.get_mem_ground])]




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
