module

public import Mathlib.Algebra.Order.Interval.Set.SuccPred
public import Mathlib.Data.Set.Card
public import Matroid.ForMathlib.Interval
public import Matroid.ForMathlib.Parity
public import Matroid.ForMathlib.List.Extract
public import Mathlib.Order.Interval.Finset.Nat

@[expose] public section

variable {α : Type*} {L l : List α} {x : α} {i j p q n : ℕ}

open Set

namespace List


lemma Nodup.toSet_inj_of_sublist (hl : l.Nodup) {k k' : List α} (hkl : k <+ l) (hk'l : k' <+ l) :
    {x | x ∈ k} = {x | x ∈ k'} ↔ k = k' := by
  refine ⟨fun h ↦ ?_, fun h ↦ by simp [h]⟩
  induction l generalizing k k' with
  | nil => rw [show k = [] by simpa using hkl, show k' = [] by simpa using hk'l]
  | cons x l ih =>
    rw [sublist_cons_iff] at hk'l hkl
    obtain hk'l | ⟨k', rfl, hk'⟩ := hk'l
    · obtain hkl | ⟨k, rfl, hk⟩ := hkl
      · exact ih (by grind) hkl hk'l h
      simp only [nodup_cons] at hl
      exact False.elim <| hl.1 <| hk'l.mem <| h.subset <| by simp
    simp only [nodup_cons] at hl
    obtain hkl | ⟨k, rfl, hk⟩ := hkl
    · exact False.elim <| hl.1 <| hkl.mem <| h.symm.subset <| by simp
    simp only [mem_cons, ofPred_or, ofPred_eq_eq_singleton, singleton_union] at h
    rw [ih (by grind) hk hk']
    rw [← insert_sdiff_self_of_notMem (s := {x | x ∈ k}) (a := x), h,
      insert_sdiff_self_of_notMem]
    · exact fun h ↦ hl.1 <| hk'.mem h
    exact fun h ↦ hl.1 <| hk.mem h

@[simp]
lemma toSet_disjoint {l l' : List α} :
    _root_.Disjoint ({x | x ∈ l} : Set α) {x | x ∈ l'} ↔ Disjoint l l' := by
  simp [disjoint_left, Set.disjoint_left]

alias ⟨_, Disjoint.toSet⟩ := toSet_disjoint

lemma subset_of_subset_toSet_of_forall {s t : Set α} (hs : s ⊆ {x | x ∈ l})
    (hst : ∀ i (hi : i < l.length), l[i] ∈ s → l[i] ∈ t) : s ⊆ t := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := getElem_of_mem <| hs hx
  exact hst i hi hx

lemma eq_of_subset_toSet_of_forall {s t : Set α} (hs : s ⊆ {x | x ∈ l}) (ht : t ⊆ {x | x ∈ l})
    (hst : ∀ i (hi : i < l.length), l[i] ∈ s ↔ l[i] ∈ t) : s = t :=
  (subset_of_subset_toSet_of_forall hs (by grind)).antisymm <|
    (subset_of_subset_toSet_of_forall ht (by grind))

@[simp]
lemma toSet_nonempty_iff : {x | x ∈ l}.Nonempty ↔ l ≠ [] := by
  cases l with
  | nil => simp
  | cons head tail =>
    rw [toSet_cons_eq]
    simp

/-- The set `{L[i] | i ∈ s}` for some set `s`. -/
def getElems (L : List α) (s : Set ℕ) : Set α :=
  {x | ∃ (i : ℕ) (hi : i < L.length), i ∈ s ∧ L[i] = x}

@[simp]
lemma getElems_finite (L : List α) (s : Set ℕ) : (L.getElems s).Finite :=
  L.finite_toSet.subset <| by grind [getElems]

@[simp]
lemma nil_getElems (s : Set ℕ) : ([] : List α).getElems s = ∅ := by
  simp [getElems]

@[simp]
lemma getElems_empty (L : List α) : L.getElems ∅ = ∅ := by
  simp [getElems]

@[gcongr]
lemma getElems_mono (L : List α) {s t : Set ℕ} (hst : s ⊆ t) :
    L.getElems s ⊆ L.getElems t := by
  grind [getElems]

lemma mem_getElems {i : ℕ} {s : Set ℕ} (hi : i ∈ s) (hlt : i < L.length) : L[i] ∈ L.getElems s :=
  ⟨i, hlt, hi, rfl⟩

lemma getElems_union (L : List α) (s t : Set ℕ) :
    L.getElems (s ∪ t) = L.getElems s ∪ L.getElems t := by
  refine (Set.union_subset (getElems_mono _ (by simp)) (getElems_mono _ (by simp))).antisymm' ?_
  rintro _ ⟨i, hi, hi', rfl⟩
  exact Or.elim hi' (fun h ↦ .inl (mem_getElems h hi)) fun h ↦ .inr (mem_getElems h hi)

lemma getElems_singleton {i : ℕ} (hi : i < L.length) : L.getElems {i} = {L[i]} := by
  grind [getElems]

@[simp]
lemma Nodup.getElem_mem_getElems_iff (hL : L.Nodup) {s i} {hi : i < L.length} :
    L[i] ∈ L.getElems s ↔ i ∈ s := by
  simp [getElems, hL.getElem_inj_iff, hi]

lemma getElems_insert (L : List α) (s : Set ℕ) {i : ℕ} (hi : i < L.length) :
    L.getElems (insert i s) = insert L[i] (L.getElems s) := by
  rw [← union_singleton, getElems_union, getElems_singleton hi, union_singleton]

lemma getElems_insert_eq_self (L : List α) (s : Set ℕ) {i : ℕ} (hi : L.length ≤ i) :
    L.getElems (insert i s) = L.getElems s := by
  rw [← union_singleton, getElems_union]
  simp [getElems, hi]

lemma getElems_insert_eq_dite (L : List α) (s : Set ℕ) (i : ℕ) :
    L.getElems (insert i s) = if hi : i < L.length then insert L[i] (L.getElems s) else
      L.getElems s := by
  split_ifs with h
  · exact getElems_insert L s h
  exact getElems_insert_eq_self L s (by lia)

lemma Nodup.getElems_insert_sdiff (hL : L.Nodup) (s : Set ℕ) (his : i ∉ s) (hi : i < L.length) :
    L.getElems (insert i s) \ {L[i]} = L.getElems s := by
  rw [getElems_insert_eq_dite, dite_eq_left hi, insert_sdiff_self_of_notMem]
  rwa [hL.getElem_mem_getElems_iff]

lemma getElems_singleton_subsingleton {i : ℕ} : (L.getElems {i}).Subsingleton := by
  by_cases hi : i < L.length
  · simp [getElems_singleton hi]
  simp [getElems, hi]

lemma getElems_cons_of_mem (L : List α) (a : α) {s : Set ℕ} (h0 : 0 ∈ s) :
    (a :: L).getElems s = insert a (L.getElems {x | x + 1 ∈ s}) := by
  refine Set.ext fun x ↦ ⟨?_, ?_⟩
  · rintro ⟨rfl | i, hi, his, rfl⟩ <;> simp [mem_getElems, his]
  rintro (rfl | ⟨i, hi, his, rfl⟩)
  · exact mem_getElems h0 (L := x :: L) (by simp)
  exact mem_getElems (show i + 1 ∈ s from his) (L := a :: L) (by grind)

lemma getElems_cons_of_notMem (L : List α) (a : α) {s : Set ℕ} (h0 : 0 ∉ s) :
    (a :: L).getElems s = L.getElems {x | x + 1 ∈ s} := by
  refine Set.ext fun x ↦ ⟨?_, ?_⟩
  · rintro ⟨rfl | i, hi, his, rfl⟩
    · contradiction
    simp [mem_getElems, his]
  rintro ⟨i, hi, his, rfl⟩
  exact mem_getElems (show i + 1 ∈ s from his) (L := a :: L) (by grind)

lemma getElems_cons (L : List α) (a : α) (s : Set ℕ) [Decidable (0 ∈ s)] :
    (a :: L).getElems s = if 0 ∈ s then insert a (L.getElems {x | x + 1 ∈ s}) else
      L.getElems {x | x + 1 ∈ s} := by
  split_ifs with h
  · rw [getElems_cons_of_mem _ _ h]
  rw [getElems_cons_of_notMem _ _ h]

lemma getElems_single_of_notMem {s : Set ℕ} (h : 0 ∉ s) (x : α) : [x].getElems s = ∅ := by
  simp [getElems_cons_of_notMem _ _ h]

lemma getElems_single_of_mem {s : Set ℕ} (h : 0 ∈ s) (x : α) : [x].getElems s = {x} := by
  simp [getElems_cons_of_mem _ _ h]

lemma getElems_single (s : Set ℕ) [Decidable (0 ∈ s)] (x : α) :
    [x].getElems s = if 0 ∈ s then {x} else ∅ := by
  split_ifs with h
  · simp [getElems_cons_of_mem _ _ h]
  simp [getElems_cons_of_notMem _ _ h]

lemma getElems_encard_le (L : List α) (s : Set ℕ) : (L.getElems s).encard ≤ s.encard := by
  obtain hs | hs := s.finite_or_infinite.symm
  · simp [hs.encard_eq]
  induction s, hs using Set.Finite.induction_on with
  | empty => simp
  | @insert a s has hs ih =>
    grw [← Set.singleton_union, getElems_union, Set.encard_union_le,
      Set.encard_le_one_iff_subsingleton.2 (getElems_singleton_subsingleton ..), ih,
      Set.singleton_union, Set.encard_insert_of_notMem has, add_comm]
@[simp]
lemma getElems_univ (L : List α) : L.getElems Set.univ = {x | x ∈ L} := by
  refine Set.ext fun x ↦ ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨i, hi, -, rfl⟩
    simp
  obtain ⟨i, hi, rfl⟩ := getElem_of_mem h
  exact ⟨i, hi, by simp, rfl⟩

@[grind! .]
lemma getElems_subset_toSet (L : List α) (s : Set ℕ) : L.getElems s ⊆ {x | x ∈ L} := by
  grw [s.subset_univ, getElems_univ]

lemma getElems_congr (L : List α) {s t : Set ℕ} (hst : ∀ i < L.length, i ∈ s ↔ i ∈ t) :
    L.getElems s = L.getElems t := by
  grind [getElems]

lemma getElems_inter_Iio (L : List α) (s : Set ℕ) :
    L.getElems (s ∩ Set.Iio L.length) = L.getElems s :=
  getElems_congr _ <| by grind

lemma Nodup.getElems_encard_eq (hL : L.Nodup) (s) :
    (L.getElems s).encard = (s ∩ Iio L.length).encard := by
  wlog hs : s.Finite ∧ s ⊆ Iio L.length generalizing s with aux
  · rw [← getElems_inter_Iio, aux _ ⟨(finite_Iio L.length).inter_of_right _, by simp⟩, inter_assoc,
      inter_self]
  obtain ⟨hfin, hs⟩ := hs
  induction s, hfin using Finite.induction_on with
  | empty => simp
  | @insert a s has hfin ih =>
    rw [getElems_insert _ _ (by grind), encard_insert_of_notMem, inter_eq_self_of_subset_left hs,
      encard_insert_of_notMem has, ih (by grind), inter_eq_self_of_subset_left (by grind)]
    simpa [hL.getElem_mem_getElems_iff]

lemma Nodup.getElems_subset_getElems_iff (hL : L.Nodup) {s t : Set ℕ} :
    L.getElems s ⊆ L.getElems t ↔ (s ∩ Iio L.length) ⊆ (t ∩ Iio L.length) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · exact fun i ⟨his, hiL⟩ ↦ ⟨hL.getElem_mem_getElems_iff.1 <| h (mem_getElems his hiL), hiL⟩
  grw [← getElems_inter_Iio, h, getElems_inter_Iio]

lemma Nodup.getElems_eq_getElems_iff (hL : L.Nodup) {s t : Set ℕ} :
    L.getElems s = L.getElems t ↔ (s ∩ Iio L.length) = (t ∩ Iio L.length) := by
  simp [subset_antisymm_iff, hL.getElems_subset_getElems_iff]

lemma Nodup.getElems_disjoint_iff (hL : L.Nodup) {s t} :
    _root_.Disjoint (L.getElems s) (L.getElems t) ↔
    _root_.Disjoint (s ∩ Iio L.length) (t ∩ Iio L.length) := by
  simp +contextual only [Set.disjoint_left, Set.mem_inter_iff, mem_Iio, and_true, and_imp]
  refine ⟨fun h a has hal ↦ ?_, ?_⟩
  · have hwin := h (mem_getElems has hal)
    rwa [hL.getElem_mem_getElems_iff] at hwin
  rintro h _ ⟨i, hi, hi', rfl⟩
  rw [hL.getElem_mem_getElems_iff]
  exact h hi' hi

lemma Nodup.getElems_sdiff (hL : L.Nodup) (s t : Set ℕ) :
    L.getElems (s \ t) = L.getElems s \ L.getElems t := by
  simp only [subset_antisymm_iff, subset_sdiff, hL.getElems_disjoint_iff, sdiff_subset_iff,
    ← getElems_union, union_sdiff_self]
  exact ⟨⟨getElems_mono L sdiff_subset, by grind⟩, getElems_mono _ subset_union_right⟩

lemma getElems_append (L L' : List α) (s : Set ℕ) :
    (L ++ L').getElems s = L.getElems s ∪ L'.getElems {i | i + L.length ∈ s} := by
  induction L generalizing s with
  | nil => simp
  | cons x L ih =>
    by_cases h0s : 0 ∈ s
    · simp [getElems_cons_of_mem _ _ h0s, ih, add_assoc, insert_union]
    simp [getElems_cons_of_notMem _ _  h0s, ih, add_assoc]

lemma getElems_tail (L : List α) (s : Set ℕ) : L.tail.getElems s = L.getElems ((· + 1) '' s) := by
  match L with
  | [] => simp
  | a :: L =>
    rw [tail_cons, getElems_cons_of_notMem _ _ (by simp)]
    simp

lemma getElems_dropLast (hL : L.Nodup) (hL0 : L ≠ []) (s : Set ℕ) :
    L.dropLast.getElems s = L.getElems s \ {L.getLast hL0} := by
  nth_rw 2 [← L.dropLast_concat_getLast hL0]
  grw [getElems_append, union_sdiff_distrib, sdiff_singleton_eq_self, eq_comm, union_eq_left,
    getElems_subset_toSet]
  · simp
  grw [getElems_subset_toSet, mem_ofPred_eq, getLast_eq_getElem]
  rw [← L.dropLast_concat_getLast hL0, nodup_append] at hL
  grind

lemma getElems_reverse (L : List α) (s : Set ℕ) :
    L.reverse.getElems s = L.getElems ((fun i ↦ L.length - 1 - i) ⁻¹' s) := by
  refine Set.ext fun e ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨i, hi, hiL, his, rfl⟩ := h
    exact ⟨L.length - 1 - i, by grind, by grind, by simp⟩
  obtain ⟨i, hi, h', rfl⟩ := h
  exact ⟨L.length - 1 - i, by grind, h', by grind⟩

-- lemma getElems_reverse_of_subset (L : List α) {s : Set ℕ} (hs : s ⊆ Iio L.length) :
--     L.reverse.getElems s = L.getElems ((fun i ↦ L.length - 1 - i) '' s) := by
--   rw [getElems_reverse]
--   convert rfl
--   refine image_eq_preimage_of_leftInvOn_injOn (LeftInvOn.mono ?_ hs) <|
--     InjOn.mono (preimage_mono hs) fun i hi j hj hij ↦ ?_
--   · grind [LeftInvOn]





lemma Nodup.subset_getElems_iff (hL : L.Nodup) {s : Set ℕ} {t : Set α} :
    t ⊆ L.getElems s ↔ t ⊆ {x | x ∈ L} ∧ ∀ i (hi : i < L.length), L[i] ∈ t → i ∈ s := by
  refine ⟨fun h ↦ ⟨h.trans (getElems_subset_toSet ..), fun i hi hit ↦ ?_⟩, fun h x hxt ↦ ?_⟩
  · exact hL.getElem_mem_getElems_iff.1 <| h hit
  obtain ⟨i, hi, rfl⟩ := getElem_of_mem (h.1 hxt)
  exact mem_getElems (h.2 i hi hxt) hi

lemma getElems_subset_iff {s : Set ℕ} {t : Set α} :
    L.getElems s ⊆ t ↔ ∀ i (hi : i < L.length), i ∈ s → L[i] ∈ t := by
  refine ⟨fun h i hi his ↦ h ⟨i, hi, his, rfl⟩, fun h ↦ ?_⟩
  rintro _ ⟨i, hi, his, rfl⟩
  exact h i hi his

lemma getElems_ofPred {s : Set α} (hs : s ⊆ {x | x ∈ L}) :
    s = L.getElems {i | ∃ (h : i < L.length), L[i] ∈ s} := by
  refine subset_antisymm ?_ ?_
  · intro x hxs
    obtain ⟨i, hi, rfl⟩ := getElem_of_mem (hs hxs)
    exact ⟨i, hi, ⟨hi, hxs⟩, rfl⟩
  rintro _ ⟨i, hi, hi', rfl⟩
  exact hi'.2

lemma exists_eq_getElems {s : Set α} (hs : s ⊆ {x | x ∈ L}) :
    ∃ t ⊆ Iio L.length, s = L.getElems t :=
  ⟨{i | ∃ (h : i < L.length), L[i] ∈ s}, by grind, getElems_ofPred hs⟩

lemma getElems_rotate (L : List α) (s : Set ℕ) (k : ℕ) :
    (L.rotate k).getElems s = L.getElems ((fun i ↦ (i + k) % L.length) '' (s ∩ Iio L.length)) := by
  wlog hss : s ⊆ Iio L.length generalizing s with aux
  · rw [← getElems_inter_Iio, length_rotate, aux, inter_assoc, inter_self]
    simp
  rw [inter_eq_self_of_subset_left hss]
  wlog hk1 : k = 1 generalizing L k s with aux
  · clear hk1
    induction k generalizing s with
    | zero =>
      rw [rotate_zero, EqOn.image_eq (f₂ := id), image_id]
      exact fun x hx ↦ x.mod_eq_of_lt (hss hx)
    | succ k ih =>
      by_cases h0 : L.length = 0
      · simp [show L = [] by grind]
      rw [← rotate_rotate, aux _ _ _ (by simpa) rfl, ih, image_image, length_rotate]
      · simp [show ∀ x, x + 1 + k = x + (k + 1) by lia]
      · grw [length_rotate, image_subset_range, range_subset_iff]
        grind [Nat.mod_lt]
  subst hk1
  induction L generalizing s with
  | nil => simp
  | cons x L ih =>
  simp only [rotate_cons_succ, rotate_zero, length_cons]
  have hrw (i) (hi : i < L.length) :
      i ∈ s ↔ i ∈ {x | x + 1 ∈ (fun a ↦ (a + 1) % (L.length + 1)) '' s} := by
    refine ⟨fun h ↦ ⟨i, h, Nat.mod_eq_of_lt (by simpa)⟩, fun ⟨j, hjs, (hji : _ % _ = _)⟩ ↦ ?_⟩
    rw [Nat.mod_eq_of_lt, add_left_inj] at hji
    · rwa [← hji]
    by_contra hcon
    obtain rfl : j = L.length := by grind
    simp at hji
  classical
  rw [getElems_append, getElems_single, getElems_cons, ← getElems_congr _ hrw]
  by_cases h : L.length ∈ s
  · simp only [mem_ofPred_eq, zero_add, h, ↓reduceIte, union_singleton, mem_image, left_eq_ite_iff,
      not_exists, not_and, insert_eq_self]
    exact fun h' ↦ False.elim <| h' _ h <| by simp
  simp only [mem_ofPred_eq, zero_add, h, ↓reduceIte, union_empty, mem_image, right_eq_ite_iff,
    forall_exists_index, and_imp]
  intro i hi hi0
  rw [Nat.mod_eq_of_lt (by grind)] at hi0
  simp at hi0

lemma Nodup.getElem_mem_getElems_rotate_iff (hL : L.Nodup) (s : Set ℕ) {k : ℕ} (hk : k ≤ L.length)
    {hi : i < L.length} : L[i] ∈ (L.rotate k).getElems s ↔ (i + (L.length - k)) % L.length ∈ s := by
  rw [getElems_rotate, hL.getElem_mem_getElems_iff]
  simp only [mem_image, Set.mem_inter_iff, mem_Iio]
  refine ⟨fun ⟨j, ⟨hjs, hj⟩, h'⟩ ↦ ?_, fun h ↦ ?_⟩
  · rwa [← h', Nat.mod_add_mod, add_assoc, Nat.add_sub_cancel' hk, Nat.add_mod_right,
      Nat.mod_eq_of_lt hj]
  refine ⟨_, ⟨h, Nat.mod_lt _ (by lia)⟩, ?_⟩
  rw [Nat.mod_add_mod, add_assoc, Nat.sub_add_cancel hk, Nat.add_mod_right, Nat.mod_eq_of_lt hi]

lemma getElems_rotate_of_subset {L : List α} {s : Set ℕ} (hsL : s ⊆ Iio L.length) (k : ℕ) :
    (L.rotate k).getElems s = L.getElems ((fun i ↦ (i + k) % L.length) '' s) := by
  rw [getElems_rotate, inter_eq_self_of_subset_left hsL]

lemma getElems_rotate_of_subset' {L : List α} {s : Set ℕ} {k : ℕ} (hs : s ⊆ Iio L.length)
    (hk : k ≤ L.length) : (L.rotate k).getElems s =
      L.getElems ((fun i ↦ (i + (L.length - k)) % L.length) ⁻¹' s) := by
  obtain h0 | hpos := eq_zero_or_pos L.length
  · simp [show s = ∅ by simpa [h0] using hs]
  rw [getElems_rotate_of_subset hs k, eq_comm, ← getElems_inter_Iio]
  convert rfl
  ext i
  simp only [mem_image, Set.mem_inter_iff, mem_preimage, mem_Iio]
  refine ⟨fun ⟨j, hjs, hji⟩ ↦ ?_, fun h ↦ ⟨_, h.1, ?_⟩⟩
  · rwa [← hji, Nat.mod_add_mod, add_assoc, Nat.add_sub_cancel' hk,
      Nat.add_mod_right, Nat.mod_eq_of_lt (hs hjs), and_iff_left (Nat.mod_lt _ hpos)]
  rw [Nat.mod_add_mod, ← Nat.add_sub_assoc hk, Nat.sub_add_cancel (show k ≤ i + L.length by lia),
    Nat.add_mod_right, Nat.mod_eq_of_lt h.2]

lemma getElems_rotate' {L : List α} {s : Set ℕ} {k : ℕ}
    (hk : k ≤ L.length) : (L.rotate k).getElems s =
      L.getElems ((fun i ↦ (i + (L.length - k)) % L.length) ⁻¹' s) := by
  obtain h0 | hpos := eq_zero_or_pos L.length
  · simp [length_eq_zero_iff.1 h0]
  rw [← getElems_inter_Iio, length_rotate, getElems_rotate_of_subset' (by simp) hk,
    preimage_inter, Iio, preimage_ofPred_eq]
  simp [show ∀ x, x % L.length < L.length from fun x ↦ Nat.mod_lt x hpos]

lemma getElems_rotate_bodd (L : List α) (k : ℕ) (b : Bool) (hL : L.length.bodd = false) :
    (L.rotate k).getElems {i | i.bodd = b} = L.getElems {i | i.bodd = (b != k.bodd)} := by
  obtain h0 | hpos := eq_zero_or_pos L.length
  · simp [show L = [] by simpa using h0]
  rw [← rotate_mod, ← getElems_inter_Iio, getElems_rotate_of_subset' (by simp)
    (Nat.mod_lt _ hpos).le, length_rotate, ← getElems_inter_Iio, preimage_inter, inter_assoc,
    inter_eq_self_of_subset_right (add_mod_bijOn_Iio ..).mapsTo.subset_preimage,
    getElems_inter_Iio]
  simp only [preimage_ofPred_eq, Nat.mod_bodd hL, Nat.bodd_add, xor,
    Nat.bodd_sub (Nat.mod_lt _ hpos).le, hL, Bool.false_bne]
  grind [cases Bool]

lemma Nodup.getElems_eq_iff (hL : L.Nodup) {s : Set ℕ} {t : Set α} :
    t = L.getElems s ↔ t ⊆ {x | x ∈ L} ∧ ∀ i (hi : i < L.length), L[i] ∈ t ↔ i ∈ s := by
  refine ⟨fun h ↦ ⟨h.subset.trans (getElems_subset_toSet ..), fun i hi ↦ ?_⟩, fun h ↦ ?_⟩
  · rw [h, hL.getElem_mem_getElems_iff]
  refine subset_antisymm ?_ ?_
  · grind [subset_getElems_iff]
  grind [getElems_subset_iff]

lemma Nodup.getElems_inter (hL : L.Nodup) (s t : Set ℕ) :
    L.getElems (s ∩ t) = L.getElems s ∩ L.getElems t := by
  suffices L.getElems s ∩ L.getElems t ⊆ {x | x ∈ L} by
    simpa [eq_comm, hL.getElems_eq_iff, hL.getElem_mem_getElems_iff]
  grw [getElems_subset_toSet, Set.inter_subset_left]

lemma Nodup.getElems_ofPred_and (hL : L.Nodup) (s : Set ℕ) (p : ℕ → Prop) :
    L.getElems {i ∈ s | p i} = L.getElems s ∩ L.getElems {i | p i} := by
  rw [ofPred_and, hL.getElems_inter, ofPred_mem_eq]

lemma getElems_Ico_eq_singleton (L : List α) (p : ℕ) (hp : p < L.length) :
    L.getElems (Set.Ico p (p + 1)) = {L[p]} := by
  simp [getElems, ← le_antisymm_iff, eq_comm (a := L[p]), hp]

lemma getElems_Ico_eq_pair (L : List α) (p : ℕ) (hp : p + 1 < L.length) :
    L.getElems (Set.Ico p (p + 2)) = {L[p], L[p + 1]} := by
  rw [show p + 2 = (p + 1) + 1 by simp, ← insert_Ico_right_eq_Ico_add_one (by lia),
    getElems_insert _ _ hp, getElems_Ico_eq_singleton _ _ (by lia), pair_comm]

lemma getElems_Ico_eq_triple (L : List α) (p : ℕ) (hp : p + 2 < L.length) :
    L.getElems (Set.Ico p (p + 3)) = {L[p], L[p + 1], L[p + 2]} := by
  rw [show p + 3 = (p + 2) + 1 by simp, ← insert_Ico_right_eq_Ico_add_one (by lia),
    getElems_insert _ _ hp, getElems_Ico_eq_pair _ _ (by lia), insert_comm, pair_comm]

lemma getElems_reverse_bodd (L : List α) (b : Bool) :
    L.reverse.getElems {i | i.bodd = b} = L.getElems {i | i.bodd = (b == L.length.bodd)} := by
  suffices aux : ∀ (L : List α) b,
      L.reverse.getElems {i | i.bodd = b} ⊆ L.getElems {i | i.bodd = (b == L.length.bodd)} by
    refine (aux ..).antisymm ?_
    nth_grw 1 [← L.reverse_reverse, aux, length_reverse]
    simp
  rintro L b _ ⟨i, hi, rfl, rfl⟩
  refine ⟨L.length - 1 - i, by grind, ?_, by simp⟩
  simp only [mem_ofPred_eq]
  obtain ⟨d, hd⟩ := exists_add_of_le (show i + 1 ≤ L.length by grind)
  rw [hd, ← Nat.sub_add_eq, add_comm 1, Nat.add_sub_cancel_left]
  cases h : i.bodd with simp [h]

lemma getElems_bodd_eq_reverse (L : List α) (b : Bool) :
    L.getElems {i | i.bodd = b} = L.reverse.getElems {i | i.bodd = (b == L.length.bodd)} := by
  simp [getElems_reverse_bodd]

lemma Nodup.getElems_bodd_encard (hL : L.Nodup) (b : Bool) :
    2 * (L.getElems {i | i.bodd = b}).encard + b.toNat =
      L.length + (b != L.length.bodd).toNat := by
  rw [hL.getElems_encard_eq, inter_comm, encard_Iio_inter_bodd L.length b]

lemma Nodup.getElems_bodd_encard_of_even (hL : L.Nodup) (b : Bool) (hlen : L.length.bodd = false) :
    2 * (L.getElems {i | i.bodd = b}).encard = L.length := by
  simpa [hlen] using hL.getElems_bodd_encard b

@[simp]
lemma getElems_Iio_length (L : List α) : L.getElems (Set.Iio L.length) = {x | x ∈ L} := by
  rw [← Set.univ_inter (Set.Iio L.length), getElems_inter_Iio, getElems_univ]

lemma getElems_Iio (L : List α) (p : ℕ) : L.getElems (Set.Iio p) = {x | x ∈ L.take p} := by
  obtain hle | hlt := le_or_gt L.length p
  · rw [take_of_length_le (by lia), ← getElems_inter_Iio, inter_eq_self_of_subset_right (by simpa),
      getElems_Iio_length]
  induction L generalizing p with
  | nil => simp
  | cons x L ih =>
    obtain rfl | p := p
    · simp
    rw [getElems_cons_of_mem L x (by simp), take_succ_cons]
    simp [mem_Iio, Order.lt_add_one_iff, Order.add_one_le_iff, mem_cons, ofPred_or, ← ih p
      (by simpa using hlt), Set.Iio_def]

lemma getElems_Ici (L : List α) (p : ℕ) : L.getElems (Set.Ici p) = {x | x ∈ L.drop p} := by
  induction L generalizing p with
  | nil => simp
  | cons x L ih =>
    obtain rfl | p := p
    · simp
    rw [getElems_cons_of_notMem _ _ (by simp), drop_succ_cons, ← ih _]
    simp [Ici]

lemma getElems_Ico (L : List α) (p q : ℕ) : L.getElems (Set.Ico p q) = {x | x ∈ L.extract p q} := by
  induction L generalizing p q with
  | nil => simp
  | cons x L ih =>
    obtain rfl | p := p
    · rw [extract_zero, ← getElems_Iio, Ico_zero]
    obtain rfl | q := q
    · simp
    rw [getElems_cons_of_notMem _ _ (by simp)]
    simp_rw [mem_Ico, add_le_add_iff_right, add_lt_add_iff_right, ← mem_Ico, ofPred_mem_eq, ih,
      extract_succ_cons]
