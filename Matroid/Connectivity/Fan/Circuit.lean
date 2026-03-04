import Matroid.Connectivity.Fan.Basic

open Set List

namespace Matroid

set_option linter.style.longLine false

variable {α : Type*} {M : Matroid α} {X Y C K T : Set α} {e f g x y : α} {b c d : Bool}
    {J : Bool → List α} {L : List α} {n i j : ℕ} {F J : List α} {b c : Bool} {L : List ℕ}

variable {P Q : Finset ℕ}

namespace Fan


/-- A subset of indices of a fan is `Orthogonal` if it does not intersect any triad
in exactly one element. The set of indices of a matroid circuit must have this property. -/
inductive Orthogonal : ℕ → Bool → Finset ℕ → Prop
  | small {n b P} (hn : n ≤ 2) (hP : P ⊆ Finset.range n) : Orthogonal n b P
  | succ_of_not' (n b P) (h : Orthogonal n (!b) P) (hn : 2 ≤ n)
      (hb : b = true → (0 ∈ P ↔ 1 ∈ P)) : Orthogonal (n + 1) b (P.map (addRightEmbedding 1))
  | insert_succ_of_not' (n b P) (h : Orthogonal n (!b) P) (hn : 2 ≤ n)
      (hb : b = true → (0 ∈ P ∨ 1 ∈ P)) :
      Orthogonal (n + 1) b (insert 0 <| P.map (addRightEmbedding 1))

lemma Orthogonal.subset_range (h : Orthogonal n b P) : P ⊆ Finset.range n := by
  induction h with
  | small => assumption
  | succ_of_not' n b P h hle hb ih => grw [ih, Finset.range_add_one',
    ← Finset.subset_insert, addRightEmbedding]
  | insert_succ_of_not' n b P h hle hb ih => grw [ih, Finset.range_add_one', addRightEmbedding]

lemma Orthogonal.succ (h : Orthogonal n b P) (hb : b = false → (0 ∈ P ↔ 1 ∈ P)) :
    Orthogonal (n + 1) (!b) (P.map (addRightEmbedding 1)) := by
  obtain hle | hlt := le_or_gt n 1
  · refine Orthogonal.small (by lia) ?_
    grw [h.subset_range, Finset.range_add_one', ← Finset.subset_insert, addRightEmbedding]
  exact (b.not_not ▸ h).succ_of_not' _ _ _ hlt (by simpa)

lemma Orthogonal.insert_succ (h : Orthogonal n b P) (hb : b = false → (0 ∈ P ∨ 1 ∈ P)) :
    Orthogonal (n + 1) (!b) <| insert 0 (P.map (addRightEmbedding 1)) := by
  obtain hle | hlt := le_or_gt n 1
  · refine Orthogonal.small (by lia) ?_
    grw [h.subset_range, Finset.range_add_one', addRightEmbedding]
  apply (b.not_not ▸ h).insert_succ_of_not' <;> simpa

lemma Orthogonal.succ_of_not (h : Orthogonal n (!b) P) (hb : b = true → (0 ∈ P ↔ 1 ∈ P)) :
    Orthogonal (n + 1) b (P.map (addRightEmbedding 1)) := by
  simpa using h.succ (by simpa)

lemma Orthogonal.insert_succ_of_not (h : Orthogonal n (!b) P) (hb : b = true → (0 ∈ P ∨ 1 ∈ P)) :
    Orthogonal (n + 1) b (insert 0 <| P.map (addRightEmbedding 1)) := by
  simpa using h.insert_succ (by simpa)

lemma orthogonal_of_le_two (hn : n ≤ 2) : Orthogonal n b P ↔ P ⊆ Finset.range n :=
  ⟨fun h ↦ h.subset_range, Orthogonal.small hn⟩

@[simp]
lemma orthogonal_zero : Orthogonal 0 b P ↔ P = ∅ := by
  rw [orthogonal_of_le_two (by simp), Finset.range_zero, Finset.subset_empty]

@[simp]
lemma orthogonal_one : Orthogonal 1 b P ↔ P = ∅ ∨ P = {0} := by
  rw [orthogonal_of_le_two (by simp), Finset.range_one, Finset.subset_singleton_iff]

@[simp]
lemma orthogonal_two : Orthogonal 2 b P ↔ P ⊆ {0, 1} :=
  orthogonal_of_le_two rfl.le

@[simp]
lemma orthogonal_empty : Orthogonal n b ∅ := by
  induction n generalizing b with
  | zero => simp
  | succ n ih => simpa using (@ih (!b)).succ (by simp)

lemma orthogonal_three (hP : P ⊆ Finset.range 3) (hbL : b = true → P.card ≠ 1) :
    Orthogonal 3 b P := by
  rw [Finset.range_add_one', Finset.subset_insert_iff, Finset.subset_map_iff] at hP
  obtain ⟨Q, hQ, hQP⟩ := hP
  by_cases h0 : 0 ∈ P
  · rw [← Finset.insert_erase h0, hQP] at hbL ⊢
    refine Orthogonal.insert_succ_of_not (by simpa) fun hb ↦ ?_
    grind [show Q ≠ ∅ by simpa [hb] using hbL]
  rw [← Finset.erase_eq_of_notMem h0, hQP] at hbL ⊢
  exact Orthogonal.succ_of_not (by simpa) fun hb ↦ by grind [Finset.subset_range_two]

/-- The intersection of a fan with a circuit satisfies `FCI`. -/
lemma Isinter_circuit_orthogonal (h : M.IsFan F b c) (hC : M.IsCircuit C)
    [DecidablePred (· ∈ C)] : Orthogonal F.length b (F.findIdxs (· ∈ C)).toFinset := by
  classical
  induction h with
  | of_pair b e f he hf hne =>
    simp only [length_cons, length_nil, zero_add, Nat.reduceAdd, findIdxs_cons, orthogonal_two]
    split_ifs <;> simp
  | cons_triangle e x y F b c h heF hT ih =>
    by_cases heC : e ∈ C
    · rw [findIdxs_cons, if_pos (by simpa), findIdxs_start, zero_add,
        List.map_congr_left (g := addRightEmbedding 1) (by simp), toFinset_cons,
        List.map_toFinset_embedding]
      refine ih.insert_succ fun hb ↦ ?_
      simp only [findIdxs_cons, List.mem_toFinset]
      grind [hT.mem_or_mem_of_isCircuit_bDual (K := C) (by simpa [hb]) (by simpa using heC)]
    rw [findIdxs_cons, if_neg (by simpa), zero_add, findIdxs_start,
      List.map_congr_left (g := addRightEmbedding 1) (by simp), List.map_toFinset_embedding]
    refine ih.succ fun hb ↦ ?_
    simp only [findIdxs_cons, List.mem_toFinset]
    grind [hT.mem_iff_mem_of_isCircuit_bDual (K := C) (by simpa [hb]) (by simpa using heC)]

lemma Orthogonal.mem_one_or_two (h : Orthogonal n true P) (hn : 3 ≤ n) (h0 : 0 ∈ P) :
    1 ∈ P ∨ 2 ∈ P := by
  cases h with grind

lemma Orthogonal.mem_one_iff_two (h : Orthogonal n true P) (hn : 3 ≤ n) (h0 : 0 ∉ P) :
    1 ∈ P ↔ 2 ∈ P := by
  cases h with grind



-- @[elab_as_elim]
-- lemma Orthogonal.rec_add_one {motive : (n : ℕ) → (b : Bool) → (P : Finset ℕ) → Orthogonal n b P → Prop}
--     (small : ∀ (n b P) (hn : n ≤ 2) (hP : P ⊆ Finset.range n), motive n b P (Orthogonal.small hn hP))
--     (succ_of_not : ∀ (n b P) (hn : 2 ≤ n) (h : Orthogonal n (!b) P) (hb : b = true → (0 ∈ P ↔ 1 ∈ P))
--       (_ih : motive n (!b) P h), motive (n + 1) b _ (h.succ_of_not hb))
--     (insert_succ_of_not : ∀ (n b P) (hn : 2 ≤ n) (h : Orthogonal n (!b) P)
--       (hb : b = true → 0 ∈ P ∨ 1 ∈ P) (_ih : motive n (!b) P h),
--        motive (n + 1) b _ (h.insert_succ_of_not hb)) {n b P} (h : Orthogonal (n + 1) b P) :
--     motive _ _ _ h := by

-- @[elab_as_elim]
-- lemma Orthogonal.rec_add_two {motive : (n : ℕ) → (b : Bool) → (P : Finset ℕ) → Orthogonal n b P → Prop}
--     (small : ∀ (n b P) (hn : n ≤ 2) (hP : P ⊆ Finset.range n), motive n b P (Orthogonal.small hn hP))
--     (succ_of_not : ∀ (n b P) (hn : 2 ≤ n) (h : Orthogonal n (!b) P) (hb : b = true → (0 ∈ P ↔ 1 ∈ P))
--       (_ih : motive n (!b) P h), motive (n + 1) b _ (h.succ_of_not hb))
--     (insert_succ_of_not : ∀ (n b P) (hn : 2 ≤ n) (h : Orthogonal n (!b) P)
--       (hb : b = true → 0 ∈ P ∨ 1 ∈ P) (_ih : motive n (!b) P h),
--        motive (n + 1) b _ (h.insert_succ_of_not hb)) {n b P} (h : Orthogonal (n + 2) b P) :
--     motive _ _ _ h := by
--   sorry

lemma Orthogonal.mem_or_mem_right (h : Orthogonal n b P) (hin : i + 2 < n)
    (hi : i.bodd = !b) (hiP : i ∈ P) : i + 1 ∈ P ∨ i + 2 ∈ P := by
  induction h generalizing i with
  | small => lia
  | succ_of_not' n b P h hle hb ih =>
    cases i with
    | zero => simp at hiP
    | succ i => simpa using ih (i := i) (by lia) (by simpa using hi) (by simpa using hiP)
  | insert_succ_of_not' n b P h hle hb ih =>
    cases i with
    | zero => simpa using hb (by simpa using hi)
    | succ i => simpa using ih (i := i) (by lia) (by simpa using hi) (by simpa using hiP)

lemma Orthogonal.mem_iff_mem_right (h : Orthogonal n b P) (hin : i + 2 < n)
    (hi : i.bodd = !b) (hiP : i ∉ P) : i + 1 ∈ P ↔ i + 2 ∈ P := by
  induction h generalizing i with
  | small => lia
    | succ_of_not' n b P h hle hb ih =>
    cases i with
    | zero => simpa using hb (by simpa using hi)
    | succ i => simpa using ih (i := i) (by lia) (by simpa using hi) (by simpa using hiP)
  | insert_succ_of_not' n b P h hle hb ih =>
    cases i with
    | zero => simp at hiP
    | succ i => simpa using ih (i := i) (by lia) (by simpa using hi) (by simpa using hiP)

lemma Orthogonal.mem_or_mem_left_right (h : Orthogonal n b P) (hin : i + 2 < n)
    (hi : i.bodd = !b) (hiP : i + 1 ∈ P) : i ∈ P ∨ i + 2 ∈ P := by
  grind [h.mem_iff_mem_right hin hi]

lemma Orthogonal.mem_iff_mem_left_right (h : Orthogonal n b P) (hin : i + 2 < n)
    (hi : i.bodd = !b) (hiP : i + 1 ∉ P) : i ∈ P ↔ i + 2 ∈ P := by
  grind [h.mem_or_mem_right hin hi, h.mem_iff_mem_right hin hi]

lemma Orthogonal.mem_or_mem_left (h : Orthogonal n b P) (hi : i.bodd = !b)
    (hiP : i + 2 ∈ P) : i ∈ P ∨ i + 1 ∈ P := by
  grind [h.mem_iff_mem_right (by simpa using Finset.mem_of_subset h.subset_range hiP) hi]

lemma Orthogonal.mem_iff_mem_left (h : Orthogonal n b P) (hin : i + 2 < n)
    (hi : i.bodd = !b) (hiP : i + 2 ∉ P) : i ∈ P ↔ i + 1 ∈ P := by
  grind [h.mem_iff_mem_right hin hi, h.mem_or_mem_right hin hi]

lemma Orthogonal.card_inter_triad_ne_one (h : Orthogonal n b P) (hin : i + 2 < n)
    (hi : i.bodd = !b) : ({i, i + 1, i + 2} ∩ P).card ≠ 1 := by
  grind [h.mem_or_mem_left hi, h.mem_iff_mem_left]

lemma Orthogonal.succ_right (h : Orthogonal (n + 2) b P)
    (hnb : b = !n.bodd → (n ∈ P ↔ n + 1 ∈ P)) : Orthogonal (n + 3) b P := by
  generalize hm : n + 2 = m at h
  induction h generalizing n with
  | small => grind [orthogonal_three, Finset.subset_range_two, Nat.bodd_zero]
  | succ_of_not' m b P h hle hb ih =>
    refine Orthogonal.succ_of_not ?_ hb
    cases n with
    | zero => exact Orthogonal.small rfl.le <| h.subset_range.trans <| by grind
    | succ => exact ih (by simpa using hnb) <| by lia
  | insert_succ_of_not' m b P h hle hb ih =>
    refine Orthogonal.insert_succ_of_not ?_ hb
    cases n with
    | zero => exact Orthogonal.small rfl.le <| h.subset_range.trans <| by grind
    | succ n => exact ih (by simpa using hnb) <| by lia

lemma Orthogonal.cons_succ_right (h : Orthogonal (n + 2) b P)
    (hnb : b = !n.bodd → (n ∈ P ∨ n + 1 ∈ P)) :
    Orthogonal (n + 3) b (P.cons (n + 2) (by grind [h.subset_range])) := by
  generalize_proofs hnP
  rw [Finset.cons_eq_insert]
  generalize hm : n + 2 = m at h
  induction h generalizing n with
  | small => grind [orthogonal_three, Finset.subset_range_two, Nat.bodd_zero]
  | succ_of_not' m b P h hle hb ih =>
    cases n with
    | zero => exact orthogonal_three (by grind [h.subset_range]) <| by grind [Nat.bodd_zero]
    | succ n => simpa [add_right_comm] using
        (ih (by simpa using hnb) (by grind) (by lia)).succ_of_not (by grind)
  | insert_succ_of_not' m b P h hle hb ih =>
    cases n with
    | zero => exact orthogonal_three (by grind [h.subset_range]) <| by grind
    | succ n => simpa [Finset.insert_comm, add_right_comm] using
        (ih (by simpa using hnb) (by grind) (by lia)).insert_succ_of_not (by grind)

lemma Orthogonal.erase_of_succ (h : Orthogonal (n + 1) b P) :
    Orthogonal n b (P.erase n) := by
  generalize hmn : n + 1 = m at h
  induction h generalizing n with
  | small => exact Orthogonal.small (by lia) <| by grind
  | succ_of_not' m b P h hle hb ih =>
    obtain rfl : n = m := by lia
    obtain rfl | rfl | rfl | n := n; lia; lia; grind [orthogonal_of_le_two hle, h.subset_range]
    rw [show n + 3 = addRightEmbedding 1 (n + 2) from rfl, ← Finset.map_erase]
    exact (ih (n := n + 2) (by lia)).succ_of_not <| by simpa
  | insert_succ_of_not' m b P h hn hb ih =>
    obtain rfl : n = m := by lia
    obtain rfl | rfl | rfl | n := n; lia; lia; grind [orthogonal_two, h.subset_range]
    rw [show n + 3 = addRightEmbedding 1 (n + 2) from rfl, Finset.erase_insert_of_ne (by grind),
      ← Finset.map_erase]
    exact (ih (by lia)).insert_succ_of_not <| by simpa

lemma Orthogonal.of_succ (h : Orthogonal (n + 1) b P) (hP : n ∉ P) :
    Orthogonal n b P := by
  rw [← Finset.erase_eq_of_notMem hP]
  exact h.erase_of_succ

lemma Orthogonal.of_succ_insert (h : Orthogonal (n + 1) b (insert n P)) (hP : n ∉ P) :
    Orthogonal n b P := by
  rw [← Finset.erase_insert hP]
  exact h.erase_of_succ

@[elab_as_elim]
lemma Orthogonal.induction_right
    {motive : (n : ℕ) → (b : Bool) → (P : Finset ℕ) → Orthogonal n b P → Prop}
    (small : ∀ (n b P) (hn : n ≤ 2) (hP : P ⊆ Finset.range n),
      motive n b P (Orthogonal.small hn hP))
    (succ : ∀ (n b P) (h : Orthogonal (n + 2) b P) (hb : b = !n.bodd → (n ∈ P ↔ (n + 1) ∈ P))
      (_ih : motive _ _ _ h), motive (n + 3) b P (h.succ_right hb))
    (succ_cons : ∀ (n b P) (h : Orthogonal (n + 2) b P)
      (hb : b = !n.bodd → (n ∈ P ∨ (n + 1) ∈ P))
      (_ih : motive _ _ _ h), motive (n + 3) b (P.cons (n + 2) (by grind [h.subset_range]))
      (h.cons_succ_right hb))
    (h : Orthogonal n b P) : motive n b P h := by
  obtain hle | (hlt : 3 ≤ n) := le_or_gt n 2
  · grind [h.subset_range]
  obtain ⟨m, rfl⟩ := show ∃ m, n = m + 3 by obtain rfl | rfl | rfl | n := n <;> grind
  induction m generalizing P with
  | zero =>
    by_cases hmP : 2 ∈ P
    · convert succ_cons _ _ _ h.erase_of_succ ?_ (small _ _ _ rfl.le (by grind [h.subset_range]))
      · simp_rw [zero_add, Finset.cons_eq_insert, Finset.insert_erase hmP]
      rintro rfl
      grind [h.mem_one_iff_two (by lia)]
    convert succ _ _ _ h.erase_of_succ ?_ (small _ _ _ rfl.le (by grind [h.subset_range]))
    · rw [Finset.erase_eq_of_notMem hmP]
    rintro rfl
    grind [h.mem_one_iff_two (by lia), h.mem_one_or_two (by lia)]
  | succ m ih =>
    specialize ih h.erase_of_succ (by lia)
    by_cases hmP : m + 3 ∈ P
    · convert succ_cons _ _ _ h.erase_of_succ ?_ ih
      · simp [Finset.insert_erase hmP]
      rintro rfl
      simpa using h.mem_or_mem_left (by simp) hmP
    convert succ _ _ _ h.erase_of_succ ?_ ih
    · rw [Finset.erase_eq_of_notMem hmP]
    rintro rfl
    simpa using h.mem_iff_mem_left (by lia) (by simp) hmP

lemma orthogonal_triangle (hin : i + 2 < n) (hib : i.bodd = b) :
    Orthogonal n b {i, i + 1, i + 2} := by
  induction n generalizing i b with
  | zero => simp at hin
  | succ n ih =>
    obtain hlt | rfl := Nat.lt_add_one_iff_lt_or_eq.1 hin
    · obtain rfl | rfl | rfl | n := n; lia; lia; lia
      apply (ih hlt hib).succ_right
      rintro rfl
      grind [Nat.bodd_succ]
    obtain rfl | i := i
    · grind [orthogonal_three]
    simpa using (@ih i (!b) (by lia) (by simpa using hib)).succ <| by grind [Nat.bodd_eq_ite]

lemma orthogonal_of_forall_triad (hP : P ⊆ Finset.range n)
    (hib : ∀ i, i.bodd = !b → i + 2 < n → ({i, i + 1, i + 2} ∩ P).card ≠ 1) :
    Orthogonal n b P := by
  induction n generalizing P with
  | zero => grind [orthogonal_zero]
  | succ n ih =>
    obtain rfl | rfl | n := n; grind [orthogonal_one]; grind [orthogonal_two]
    obtain hn | hn := em' <| (n + 2) ∈ P
    · exact (@ih P (by grind) (by grind)).succ_right <| by rintro rfl; grind
    specialize @ih (P.erase (n + 2)) (by grind) (by grind)
    simpa [Finset.insert_erase hn] using ih.cons_succ_right (by grind)

@[mk_iff]
structure IsClosed (n : ℕ) (b : Bool) (P : Finset ℕ) : Prop where
  subset_range : P ⊆ Finset.range n
  orthogonal : Orthogonal n (!b) (Finset.range n \ P)

lemma range_isClosed (n : ℕ) (b : Bool) : IsClosed n b (Finset.range n) :=
  ⟨rfl.subset, by simp⟩

lemma isClosed_of_forall_triangle (hP : P ⊆ Finset.range n)
    (hib : ∀ i, i.bodd = b → i + 2 < n → ({i, i + 1, i + 2} ∩ P).card ≠ 2) : IsClosed n b P := by
  rw [isClosed_iff, and_iff_right hP]
  refine orthogonal_of_forall_triad (by simp) fun i hi hin hcard ↦ ?_
  rw [← Finset.inter_sdiff_left_comm, Finset.inter_eq_right.2 (by grind)] at hcard
  grind

structure Spans (n : ℕ) (b : Bool) (P : Finset ℕ) (i : ℕ) : Prop where
  subset_range : P ⊆ Finset.range n
  forall_isClosed : ∀ Q, IsClosed n b Q → P ⊆ Q → i ∈ P

lemma Spans.superset (h : Spans n b P i) (hPQ : P ⊆ Q) (hQ : Q ⊆ Finset.range n) :
    Spans n b Q i :=
  ⟨hQ, fun F hF hQF ↦ Finset.mem_of_subset hPQ <| (h.forall_isClosed F hF (hPQ.trans hQF))⟩

lemma Spans.of_mem (hP : P ⊆ Finset.range n) (hiP : i ∈ P) : Spans n b P i :=
  ⟨hP, fun _ _ _ ↦ hiP⟩

lemma Spans.lt (h : Spans n b P i) : i < n := by
  simpa using Finset.mem_of_subset h.subset_range
    <| h.forall_isClosed _ (range_isClosed n b) h.subset_range

-- lemma aux {s t : Finset ℕ} {a : ℕ} {hs : s.card = 3} (h : (s ∩ t).card = a) :
--     ∃ x y z, x ≠ y ∧ x ≠ z ∧ y ≠ z ∧ x ∈ s ∧ x ∈ t ∧ y ∈ s ∧ y ∈ t ∧ z ∈ s ∧ z ∉ t := by
--   _
example (s : Set (Fin 5)) : Finset ℕ := by
  classical
  have := s.toFinset

lemma bar {b c : Bool} (hF : M.IsFan F b c) [DecidablePred (· ∈ X)] (hX : M.IsFlat X) :

    IsClosed F.length b <| (F.get ⁻¹' X).toFinite.toFinset.map Fin.valEmbedding := by
  refine isClosed_of_forall_triangle ?_ fun i hi hin ↦ ?_
  · grw [Finset.subset_univ]
    -- grw [(findIdxs_sublist_range ..).subset.toFinset_subset, toFinset_range]

lemma bar {b c : Bool} (hF : M.IsFan F b c) [DecidablePred (· ∈ X)] (hX : M.IsFlat X) :
    IsClosed F.length b (F.findIdxs (· ∈ X)).toFinset := by
  classical
  refine isClosed_of_forall_triangle ?_ fun i hi hin ↦ ?_
  · grw [(findIdxs_sublist_range ..).subset.toFinset_subset, toFinset_range]
  intro h2
  set T : Finset ℕ := {i, i + 1, i + 2} with hT
  set U := (findIdxs (· ∈ X) F).toFinset with hU
  have hcard := Finset.card_sdiff_add_card_inter T U
  rw [h2, show Finset.card T = 1 + 2 by simp [hT], add_right_cancel_iff,
    Finset.card_eq_one] at hcard
  obtain ⟨a, ha⟩ := hcard
  have han : a < F.length := by grind [show a ∈ T \ U by grind]
  have ⟨haT, haU⟩ : a ∈ T ∧ a ∉ U := by simpa using Finset.subset_of_eq ha.symm
  suffices ha : F[a] ∈ X by simp [hU, han, ha] at haU
  have h1 := (hF.isTriangle_get _ hin).isCircuit.subset_closure_diff_singleton (F[a])
  simp only [hi, bne_self_eq_false, bDual_false] at h1
  refine mem_of_mem_of_subset (by grind) (h1.trans <| hX.closure_subset_of_subset ?_)




  -- simp [Finset.inter_insert, show i < F.length by lia, show i + 1 < F.length by lia,
  --   Finset.singleton_inter, hin]
  -- rw [Finset.card_insert_eq_ite]
  -- intro hcard
  -- by_cases hi : F[i] ∈ X
  -- · rw [Finset.insert_inter_of_mem (by simp [hi, show i < F.length by lia])] at hcard
  --   by_cases hi' : F[i+1] ∈ X
  --   · rw [Finset.insert_inter_of_mem (by simp [hi, show i + 1 < F.length by lia])] at hcard
  --     have hi2 : F[i+2] ∉ X := by
  --       simpa [← Finset.disjoint_iff_inter_eq_empty, hin] using hcard



  -- simp only [Finset.card_eq_two, ne_eq, Finset.ext_iff, Finset.mem_inter, Finset.mem_insert,
  --   Finset.mem_singleton, List.mem_toFinset, mem_findIdxs_iff_getElem_sub_pos, zero_le, tsub_zero,
  --   decide_eq_true_eq, true_and] at hcard
  -- by_cases hi : F[i] ∈ X
  -- · sorry
  -- simp [iff_def, or_imp, forall_and, hi] at hcard
  -- rw [Finset.card_eq_two] at hcard
  -- simp only [ne_eq, Finset.ext_iff, Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
  --   List.mem_toFinset, mem_findIdxs_iff_getElem_sub_pos, zero_le, tsub_zero, decide_eq_true_eq,
  --   true_and, iff_def, and_imp, forall_exists_index, or_imp, forall_and, forall_eq,
  --   show i < F.length by lia, forall_true_left, show i + 1 < F.length by lia,
  --   show i + 2 < F.length by lia] at hcard

  -- obtain ⟨x, y, hxy, h_eq⟩ := hcard

  -- obtain ⟨z, hz, hzx, hzy⟩ : ∃ z, z ∈ ({i, i + 1, i + 2} : Finset ℕ) ∧ z ≠ x ∧ z ≠ y := by
  --   simp only [Finset.mem_insert, exists_eq_or_imp, Finset.mem_singleton]
  --   grind

  -- simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  -- have h1 := (hF.isTriangle_get i hin).isCircuit.subset_closure_diff_singleton (e := F[z])
  -- simp only [← hi, bne_self_eq_false, bDual_false] at h1
  -- have h2 := hX.closure_subset_of_subset (X := {F[i], F[i+1], F[i+2]} \ {F[z]}) ?_
  -- · have h3 := mem_of_mem_of_subset (x := F[z]) (by grind) (h1.trans h2)
  --   have := Finset.mem_of_subset (Finset.subset_of_eq h_eq) (a := z)
  --   grind [List.mem_toFinset]
  -- simp [Set.subset_def]
  -- sorry













-- lemma foo {b c : Bool} (hF : M.IsFan F b c) [DecidablePred (· ∈ X)] (hXE : X ⊆ M.E)
--     (h : Spans F.length b (F.findIdxs (· ∈ X)).toFinset i) : F[i]'(h.lt) ∈ M.closure X := by
--   -- `hXE` not actually needed
