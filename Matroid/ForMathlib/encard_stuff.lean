
import Mathlib.Data.Set.Ncard
import Mathlib.Order.WithBot

section ENat

variable {n : ℕ∞}

theorem ENat.le_coe_iff {k : ℕ} : n ≤ ↑k ↔ ∃ (n₀ : ℕ), n = n₀ ∧ n₀ ≤ k :=
  WithTop.le_coe_iff

theorem ENat.exists_eq_top_or_coe (n : ℕ∞) : n = ⊤ ∨ ∃ (n₀ : ℕ), n = n₀ := by
  obtain (rfl | n) := n; exact Or.inl rfl; exact Or.inr ⟨_,rfl⟩

end ENat

section encard

namespace Set

variable {α : Type _} {s t : Set α} {x : α}

-------------------------- These can be removed after merging PR

theorem exists_intermediate_Set₁ (i : ℕ) (h : i + s.ncard ≤ t.ncard) (hst : s ⊆ t) :
    ∃ r : Set α, s ⊆ r ∧ r ⊆ t ∧ r.ncard = i + s.ncard := by
  obtain (ht | ht) := t.finite_or_infinite
  · rw [ncard_eq_toFinset_card _ (ht.subset hst)] at h ⊢
    rw [ncard_eq_toFinset_card t ht] at h
    obtain ⟨r', hsr', hr't, hr'⟩ := Finset.exists_intermediate_set _ h (by simpa)
    exact ⟨r', by simpa using hsr', by simpa using hr't, by rw [← hr', ncard_coe_Finset]⟩
  rw [ht.ncard, Nat.le_zero, add_eq_zero] at h
  exact ⟨t, hst, rfl.subset, by rw [h.1, h.2, ht.ncard, add_zero]⟩

theorem exists_intermediate_Set₁' {m : ℕ} (hs : s.ncard ≤ m) (ht : m ≤ t.ncard) (h : s ⊆ t) :
    ∃ r : Set α, s ⊆ r ∧ r ⊆ t ∧ r.ncard = m := by
  obtain ⟨r, hsr, hrt, hc⟩ :=
    exists_intermediate_Set (m - s.ncard) (by rwa [tsub_add_cancel_of_le hs]) h
  rw [tsub_add_cancel_of_le hs] at hc
  exact ⟨r, hsr, hrt, hc⟩

/-- We can shrink `s` to any smaller size. -/
theorem exists_smaller_Set (s : Set α) (i : ℕ) (h : i ≤ s.ncard) :
    ∃ t : Set α, t ⊆ s ∧ t.Finite ∧ t.ncard = i := by
  obtain (hs | hs) := s.finite_or_infinite
  · obtain ⟨r, -, hrs, hr⟩ := exists_intermediate_Set i (by simpa) (empty_subset s)
    exact ⟨r, hrs, hs.subset hrs, by simp [hr]⟩
  rw [hs.ncard, le_zero_iff] at h
  exact ⟨∅, empty_subset s, finite_empty, by simp [h]⟩

theorem Infinite.exists_supset_ncard_eq' {s t : Set α} (ht : t.Infinite) (hst : s ⊆ t)
    (hs : s.Finite) {k : ℕ} (hsk : s.ncard ≤ k) :
    ∃ s', s ⊆ s' ∧ s' ⊆ t ∧ s'.Finite ∧ s'.ncard = k := by
  obtain ⟨s₁, hs₁, hs₁fin, hs₁card⟩ := (ht.diff hs).exists_subset_ncard_eq (k - s.ncard)
  refine' ⟨s ∪ s₁, subset_union_left _ _, union_subset hst (hs₁.trans (diff_subset _ _)),
    hs.union hs₁fin, _⟩
  rwa [ncard_union_eq (disjoint_of_subset_right hs₁ disjoint_sdiff_right) hs hs₁fin, hs₁card,
    add_tsub_cancel_of_le]

---------------------------------

/-- The cardinality of a `Set` as an term in `ENat`. Infinite sets have cardinality `⊤`  -/
noncomputable def encard (s : Set α) : ℕ∞ := PartENat.withTopEquiv (PartENat.card s)

theorem Finite.encard_eq (hs : s.Finite) : s.encard = (s.ncard : ℕ∞) := by
  obtain ⟨s, rfl⟩ := hs.exists_finset_coe; simp [encard]

theorem Infinite.encard_eq (hs : s.Infinite) : s.encard = ⊤ := by
  have := hs.to_subtype; simp [encard]

@[simp] theorem encard_toNat_eq (s : Set α) : ENat.toNat s.encard = s.ncard :=
  s.finite_or_infinite.elim (fun h ↦ by simp [h.encard_eq]) (fun h ↦ by simp [h.encard_eq, h.ncard])

@[simp] theorem encard_eq_top_iff_Infinite : s.encard = ⊤ ↔ s.Infinite :=
  ⟨fun h hfin ↦ by simp [hfin.encard_eq] at h, Infinite.encard_eq⟩

@[simp] theorem encard_lt_top_iff_Finite : s.encard < ⊤ ↔ s.Finite := by
  rw [lt_top_iff_ne_top, ←not_infinite, ←encard_eq_top_iff_Infinite]

theorem encard_ne_top_iff_Finite : s.encard ≠ ⊤ ↔ s.Finite := by
  simp

theorem encard_eq_coe_iff {k : ℕ} : s.encard = k ↔ s.Finite ∧ s.ncard = k := by
  rw [←encard_ne_top_iff_Finite, ←encard_toNat_eq]
  exact ⟨fun h ↦ by simp [h], fun ⟨h1,h2⟩ ↦ by rwa [←@Nat.cast_inj ℕ∞, ENat.coe_toNat h1] at h2⟩

theorem encard_eq_iff_ncard_eq_of_ne_zero {k : ℕ} (hk : k ≠ 0) : s.encard = k ↔ s.ncard = k := by
  rw [encard_eq_coe_iff, and_iff_right_iff_imp]
  exact fun h ↦ finite_of_ncard_pos ((Nat.pos_of_ne_zero hk).trans_eq h.symm)

theorem encard_eq_succ_iff_ncard_eq_succ {k : ℕ} : s.encard = k + 1 ↔ s.ncard = k + 1 :=
  encard_eq_iff_ncard_eq_of_ne_zero (Nat.succ_ne_zero _)

theorem Finite.encard_lt_top (hs : s.Finite) : s.encard < ⊤ :=
  encard_lt_top_iff_Finite.mpr hs

theorem Finite.encard_ne_top (hs : s.Finite) : s.encard ≠ ⊤ :=
  encard_ne_top_iff_Finite.mpr hs

theorem finite_of_encard_le_coe {n : ℕ} (h : s.encard ≤ n) : s.Finite :=
  encard_lt_top_iff_Finite.mp (h.trans_lt (WithTop.coe_lt_top _))

theorem encard_le_coe_iff {n : ℕ} : s.encard ≤ n ↔ s.Finite ∧ s.ncard ≤ n := by
  simp_rw [ENat.le_coe_iff, encard_eq_coe_iff]
  exact ⟨fun ⟨n₀, he, hle⟩ ↦ ⟨he.1, he.2.trans_le hle⟩, fun ⟨h, h'⟩ ↦ ⟨_, ⟨h, rfl⟩, h'⟩⟩

theorem Finite.ncard_le_ncard_of_encard_le_encard (ht : t.Finite) (h : s.encard ≤ t.encard) :
    s.ncard ≤ t.ncard := by
  rw [ht.encard_eq, encard_le_coe_iff] at h; exact h.2

@[simp] theorem encard_eq_zero : s.encard = 0 ↔ s = ∅ := by
  rw [←ENat.coe_zero, encard_eq_coe_iff]
  exact ⟨fun ⟨h,h'⟩ ↦ by rwa [←ncard_eq_zero h],
    fun h ↦ (by simp only [h, finite_empty, ncard_empty, and_self])⟩

@[simp] theorem encard_empty : (∅ : Set α).encard = 0 := by
  rw [encard_eq_zero]

@[simp] theorem encard_singleton (x : α) : ({x} : Set α).encard = 1 := by
  rw [(finite_singleton x).encard_eq, ncard_singleton, ENat.coe_one]

theorem ncard_eq_ncard_of_encard_eq_encard (h : s.encard = t.encard) :
  s.ncard = t.ncard := by rw [←encard_toNat_eq, h, encard_toNat_eq]

theorem Finite.encard_eq_encard_of_ncard_eq_ncard (hs : s.Finite) (ht : t.Finite)
(h : s.ncard = t.ncard) : s.encard = t.encard := by rw [hs.encard_eq, ht.encard_eq, h]

theorem Finite.finite_of_encard_le (hs : s.Finite) (h : t.encard ≤ s.encard) : t.Finite := by
  rw [←encard_lt_top_iff_Finite] at *; exact h.trans_lt hs

theorem encard_insert_of_not_mem (h : x ∉ s) : (insert x s).encard = s.encard + 1 := by
  obtain (hs | hs) := s.finite_or_infinite
  · rw [hs.encard_eq, (hs.insert _).encard_eq, ncard_insert_of_not_mem h hs, Nat.cast_add,
      Nat.cast_one]
  · rw [hs.encard_eq, (hs.mono (subset_insert _ _)).encard_eq]; rfl

theorem encard_diff_singleton_add_one (h : x ∈ s) : (s \ {x}).encard + 1 = s.encard := by
  rw [←encard_insert_of_not_mem (_ : x ∉ s \ {x}), insert_diff_singleton, insert_eq_of_mem h]
  simp only [mem_diff, mem_singleton_iff, not_true, and_false, not_false_eq_true]
  
theorem encard_eq_ite (s : Set α) [Decidable (s.Finite)] :
    s.encard = if s.Finite then (s.ncard : ℕ∞) else ⊤ := by
  obtain (h | h) := s.finite_or_infinite
  · rw [h.encard_eq, if_pos h]
  rw [h.encard_eq, if_neg h]

theorem encard_subset_le (hst : s ⊆ t) : s.encard ≤ t.encard := by
  obtain (ht | ht) := t.finite_or_infinite
  · rw [ht.encard_eq, (ht.subset hst).encard_eq, Nat.cast_le]
    exact ncard_le_of_subset hst ht
  exact le_top.trans_eq ht.encard_eq.symm

theorem encard_mono : Monotone (encard : Set α → ℕ∞) :=
  fun _ _ ↦ encard_subset_le

theorem exists_supset_subset_encard_eq {k : ℕ∞} (hs : s.encard ≤ k) (ht : k ≤ t.encard)
    (hst : s ⊆ t) : ∃ r, s ⊆ r ∧ r ⊆ t ∧ r.encard = k := by
  obtain (rfl | ⟨k,rfl⟩) := k.exists_eq_top_or_coe
  · exact ⟨t, hst, rfl.subset, ht.antisymm' le_top⟩
  simp_rw [encard_eq_coe_iff]
  obtain (htfin | htinf) := t.finite_or_infinite
  · rw [Finite.encard_eq, Nat.cast_le] at hs ht
    · obtain ⟨r, hsr, hrt, rfl⟩ := exists_intermediate_Set₁' hs ht hst
      exact ⟨r, hsr, hrt, htfin.subset hrt, rfl⟩
    · exact htfin
    exact htfin.subset hst
  have hsfin := finite_of_encard_le_coe hs
  rw [hsfin.encard_eq, Nat.cast_le] at hs
  exact htinf.exists_supset_ncard_eq' hst hsfin hs

theorem exists_subset_encard_eq {k : ℕ∞} (h : k ≤ s.encard) : ∃ r, r ⊆ s ∧ r.encard = k :=
  let ⟨r, _, h'⟩ := exists_supset_subset_encard_eq (encard_empty.trans_le (zero_le k)) h
    (empty_subset s)
  ⟨r, h'⟩

theorem encard_union_eq (h : Disjoint s t) : (s ∪ t).encard = s.encard + t.encard := by
  obtain (hf | hi) := (s ∪ t).finite_or_infinite
  · obtain ⟨hs, ht⟩ := finite_union.mp hf
    rw [hf.encard_eq, hs.encard_eq, ht.encard_eq, ←Nat.cast_add, Nat.cast_inj,
      ncard_union_eq h hs ht]
  rw [hi.encard_eq]
  obtain (h | h) := infinite_union.mp hi
  · simp [h.encard_eq]
  simp [h.encard_eq]

theorem encard_diff_add_encard_inter (s t : Set α) :
    (s \ t).encard + (s ∩ t).encard = s.encard := by
  rw [←encard_union_eq (disjoint_of_subset_right (inter_subset_right _ _) disjoint_sdiff_left),
    diff_union_inter]

theorem encard_diff_add_encard_of_subset (h : s ⊆ t) :
   (t \ s).encard + s.encard = t.encard := by
  nth_rewrite 1 [←encard_diff_add_encard_inter t s]
  rw [inter_eq_self_of_subset_right h]

theorem encard_union_add_encard_inter (s t : Set α) :
  (s ∪ t).encard + (s ∩ t).encard = s.encard + t.encard :=
by rw [←diff_union_self, encard_union_eq disjoint_sdiff_left, add_right_comm,
  encard_diff_add_encard_inter]

theorem encard_union_le (s t : Set α) : (s ∪ t).encard ≤ s.encard + t.encard := by
  rw [←encard_union_add_encard_inter]; exact le_self_add

theorem finite_iff_finite_of_encard_eq_encard (h : s.encard = t.encard) : s.Finite ↔ t.Finite := by
  rw [←encard_lt_top_iff_Finite, ←encard_lt_top_iff_Finite, h]

theorem infinite_iff_infinite_of_encard_eq_encard (h : s.encard = t.encard) :
    s.Infinite ↔ t.Infinite := by rw [←encard_eq_top_iff_Infinite, h, encard_eq_top_iff_Infinite]

theorem Finite.eq_of_subset_of_encard_le (ht : t.Finite) (hst : s ⊆ t) (hts : t.encard ≤ s.encard) :
    s = t := by
  rw [ht.encard_eq, (ht.subset hst).encard_eq, Nat.cast_le] at hts
  exact eq_of_subset_of_ncard_le hst hts ht

theorem Finite.eq_of_subset_of_encard_le' (hs : s.Finite) (hst : s ⊆ t)
    (hts : t.encard ≤ s.encard) : s = t :=
  (hs.finite_of_encard_le hts).eq_of_subset_of_encard_le hst hts

theorem encard_eq_one : s.encard = 1 ↔ ∃ x, s = {x} := by
  rw [←Nat.cast_one, encard_eq_iff_ncard_eq_of_ne_zero (by simp), ncard_eq_one]

end Set

end encard