import Mathlib.Data.Set.Card
import Mathlib.Algebra.BigOperators.WithTop
import Mathlib.Algebra.BigOperators.Finprod

open Set BigOperators Function

variable {α β : Type*} {s t : Set α} {n : ℕ}

attribute [push] encard_ne_zero

attribute [gcongr] encard_le_encard

theorem Set.Finite.disjoint_of_sum_encard_le (h : (s ∪ t).Finite)
    (hle : s.encard + t.encard ≤ (s ∪ t).encard) : Disjoint s t := by
  rwa [← add_zero (encard (s ∪ t)), ← encard_union_add_encard_inter,
    WithTop.add_le_add_iff_left h.encard_lt_top.ne, nonpos_iff_eq_zero, encard_eq_zero,
    ← disjoint_iff_inter_eq_empty] at hle

theorem Set.Finite.encard_union_eq_add_encard_iff_disjoint (h : (s ∪ t).Finite) :
    s.encard + t.encard = (s ∪ t).encard ↔ Disjoint s t := by
  rw [← add_zero (encard (s ∪ t)), ← encard_union_add_encard_inter,
    WithTop.add_left_inj h.encard_lt_top.ne, encard_eq_zero, disjoint_iff_inter_eq_empty]

@[simp] theorem encard_pair_le (e f : α) : encard {e,f} ≤ 2 := by
  obtain (rfl | hne) := eq_or_ne e f
  · simp only [mem_singleton_iff, insert_eq_of_mem, encard_singleton]
    simp
  rw [encard_pair hne]

@[simp]
lemma encard_pair_iff (e f : α) : encard {e,f} = 2 ↔ e ≠ f := by
  refine ⟨?_, encard_pair⟩
  rintro h rfl
  simp at h

lemma two_le_encard_iff_nontrivial : 2 ≤ s.encard ↔ s.Nontrivial := by
  rw [← s.one_lt_encard_iff_nontrivial, ← one_add_one_eq_two, ENat.add_one_le_iff (by simp)]

theorem Set.Infinite.exists_finite_subset_encard_gt (hs : s.Infinite) (b : ℕ) :
    ∃ t ⊆ s, b < t.encard ∧ t.Finite := by
  obtain ⟨t, hts, hcard⟩ := hs.exists_subset_card_eq (b + 1)
  exact ⟨t, by simpa, by simp [encard_coe_eq_coe_finsetCard, hcard, Nat.cast_lt, - Nat.cast_add]⟩

/-- a version of `Set.Infinite.exists_finite_subset_encard_gt` with `b` of type `ℕ∞`-/
theorem Set.Infinite.exists_finite_subset_encard_gt' (hs : s.Infinite) {b : ℕ∞} (hb : b ≠ ⊤) :
    ∃ t ⊆ s, b < t.encard ∧ t.Finite := by
  lift b to ℕ using hb
  exact hs.exists_finite_subset_encard_gt b

theorem Set.coe_le_encard_iff : n ≤ s.encard ↔ (s.Finite → n ≤ s.ncard) := by
  obtain (hfin | hinf) := s.finite_or_infinite
  · rw [← hfin.cast_ncard_eq, iff_true_intro hfin, Nat.cast_le, true_imp_iff]
  rw [hinf.encard_eq, iff_true_intro le_top, true_iff, iff_false_intro hinf, false_imp_iff]
  trivial

theorem Set.encard_le_cast_iff {n : ℕ} :
    s.encard ≤ n ↔ ∃ t : Finset α, (t : Set α) = s ∧ t.card ≤ n := by
  rw [encard_le_coe_iff_finite_ncard_le]
  refine ⟨fun h ↦ ⟨h.1.toFinset, by simp, ?_⟩, ?_⟩
  · rw [ncard_eq_toFinset_card _ h.1] at h
    exact h.2
  rintro ⟨t, rfl, ht⟩
  simpa

lemma finite_of_encard_eq_ofNat {n : ℕ} [n.AtLeastTwo] (h : s.encard = ofNat(n)) : s.Finite :=
  finite_of_encard_eq_coe h

lemma finite_of_encard_eq_one (h : s.encard = 1) : s.Finite :=
  finite_of_encard_eq_coe h

theorem Equiv.encard_univ_eq (e : α ≃ β) : encard (univ : Set α) = encard (univ : Set β) := by
  rw [encard_univ, encard_univ, ENat.card_congr e]

theorem Equiv.encard_eq {s : Set α} {t : Set β} (e : s ≃ t) : s.encard = t.encard :=
  e.toEmbedding.encard_le.antisymm e.symm.toEmbedding.encard_le

theorem Fin.nonempty_embedding_iff_le_encard : Nonempty (Fin n ↪ s) ↔ n ≤ s.encard := by
  refine ⟨fun ⟨i⟩ ↦ ?_, fun h ↦ ?_⟩
  · convert ((Equiv.Set.univ (Fin n)).toEmbedding.trans i).encard_le
    simp [encard_univ]
  obtain ⟨t, hts, hcard⟩ := exists_subset_encard_eq h
  have ht : t.Finite := finite_of_encard_eq_coe hcard
  rw [← ht.cast_ncard_eq, Nat.cast_inj, ncard_eq_toFinset_card t ht] at hcard
  refine ⟨(Finset.equivFinOfCardEq hcard).symm.toEmbedding.trans ?_ ⟩
  simp only [Finite.mem_toFinset]
  exact embeddingOfSubset t s hts

@[simp] theorem encard_univ_fin (a : ℕ) : (univ : Set (Fin a)).encard = a := by
  simp [encard_eq_coe_toFinset_card]

theorem Fin.nonempty_equiv_iff_encard_eq : Nonempty (s ≃ Fin n) ↔ s.encard = n := by
  refine ⟨fun ⟨e⟩ ↦ by simpa using e.encard_univ_eq, fun h ↦ ?_⟩
  have _ := Finite.fintype (finite_of_encard_eq_coe h).to_subtype
  refine ⟨Fintype.equivFinOfCardEq <| ?_⟩
  rwa [encard_eq_coe_toFinset_card, Nat.cast_inj, toFinset_card] at h

@[simp] theorem ENat.card_option (α : Type*) : ENat.card (Option α) = ENat.card α + 1 := by
  obtain hα | hα := finite_or_infinite α
  · have _ := Fintype.ofFinite α
    simp
  simp

theorem Set.encard_biUnion {ι : Type*} {s : ι → Set α} {t : Finset ι}
    (ht : (t : Set ι).PairwiseDisjoint s) : encard (⋃ i ∈ t, s i) = ∑ i ∈ t, encard (s i) := by
  classical
  induction t using Finset.induction with | empty => simp | insert x t₀ hx IH
  rw [Finset.set_biUnion_insert, encard_union_eq, Finset.sum_insert hx, IH (ht.subset (by simp))]
  simp only [disjoint_iUnion_right]
  exact fun i hi ↦ ht (by simp) (by simp [hi]) (by rintro rfl; contradiction)

theorem Set.encard_iUnion {ι : Type*} [Fintype ι] (s : ι → Set α) (hs : Pairwise (Disjoint on s)) :
    encard (⋃ i, s i) = ∑ i, encard (s i) := by
  convert encard_biUnion (s := s) (t := Finset.univ)
  simp [show univ.PairwiseDisjoint s by rwa [← pairwise_univ] at hs]

theorem Set.encard_biUnion_le {ι : Type*} (I : Finset ι) (s : ι → Set α) :
    encard (⋃ i ∈ I, s i) ≤ ∑ i ∈ I, encard (s i) := by
  classical
  induction I using Finset.induction_on with | empty => simp | insert x J hx IH
  rw [J.set_biUnion_insert, Finset.sum_insert hx]
  exact (encard_union_le _ _).trans <| add_le_add_right IH _

theorem encard_iUnion_le {ι : Type*} [Fintype ι] (s : ι → Set α) :
    encard (⋃ i : ι, s i) ≤ ∑ i, encard (s i) := by
  simpa using encard_biUnion_le Finset.univ s

theorem Finset.pairwiseDisjoint_of_sum_encard_le_encard_biUnion {ι : Type*} {I : Finset ι}
    {s : ι → Set α} (hfin : ∀ i ∈ I, (s i).Finite)
    (hsum : ∑ i ∈ I, encard (s i) ≤ encard (⋃ i ∈ I, s i)) : (I : Set ι).PairwiseDisjoint s := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | @insert x J hx IH =>
  have hmono (K) (hK : K ⊆ insert x J) : ∑ i ∈ K, (s i).encard ≤ (⋃ i ∈ K, (s i)).encard := by
    rw [← Finset.sdiff_union_of_subset hK, Finset.sum_union Finset.sdiff_disjoint,
      Finset.set_biUnion_union] at hsum
    replace hsum := (hsum.trans (encard_union_le _ _)).trans
      (add_le_add_left (encard_biUnion_le _ s) _)
    exact WithTop.le_of_add_le_add_left
      (WithTop.sum_ne_top.2 <| fun i hi ↦ (hfin i (Finset.mem_sdiff.1 hi).1).encard_lt_top.ne) hsum
  rw [PairwiseDisjoint, Finset.coe_insert,
    pairwise_insert_of_symmetric_of_notMem (Symmetric.comap Disjoint.symm s) (by simpa),
    ← PairwiseDisjoint, and_iff_right (IH _ (hmono _ (by simp)))]
  · simp_rw [Function.onFun, Finset.mem_coe]
    refine fun b hbJ ↦ Finite.disjoint_of_sum_encard_le ?_ <|
    by simpa [Finset.sum_pair (show x ≠ b by rintro rfl; contradiction)] using
      hmono {x,b} (by simp [Finset.insert_subset_iff, hbJ])
    exact ((hfin x (by simp)).union (hfin b (by simp [hbJ])))
  exact fun i hi ↦ hfin i (by simp [hi])

theorem pairwiseDisjoint_of_sum_encard_le_encard_iUnion {ι : Type*} [Fintype ι]
    {s : ι → Set α} (hfin : ∀ i, (s i).Finite) (hsum : ∑ i, encard (s i) ≤ encard (⋃ i, s i)) :
    Pairwise (Disjoint on s) := by
  rw [← pairwise_univ, ← Finset.coe_univ]
  exact Finset.pairwiseDisjoint_of_sum_encard_le_encard_biUnion (fun i _ ↦ hfin i) (by simpa)

theorem encard_biUnion_eq_sum_iff_pairwiseDisjoint {ι : Type*} {u : Finset ι}
    {s : ι → Set α} (hs : ∀ i ∈ u, (s i).Finite) :
    encard (⋃ i ∈ u, s i) = ∑ i ∈ u, encard (s i) ↔ (u : Set ι).PairwiseDisjoint s :=
  ⟨fun h ↦ u.pairwiseDisjoint_of_sum_encard_le_encard_biUnion hs h.symm.le, encard_biUnion⟩

theorem encard_iUnion_eq_sum_iff_pairwiseDisjoint {ι : Type*} [Fintype ι] {s : ι → Set α}
    (hfin : ∀ i, (s i).Finite) :
    encard (⋃ i, s i) = ∑ i, encard (s i) ↔ Pairwise (Disjoint on s) :=
  ⟨fun h ↦ pairwiseDisjoint_of_sum_encard_le_encard_iUnion hfin h.symm.le, encard_iUnion s⟩

theorem Set.Finite.encard_le_iff_nonempty_embedding {s : Set α} {t : Set β} (hs : s.Finite) :
    s.encard ≤ t.encard ↔ Nonempty (s ↪ t) := by
  cases isEmpty_or_nonempty β
  · simp only [t.eq_empty_of_isEmpty, encard_empty, nonpos_iff_eq_zero, encard_eq_zero]
    constructor; rintro rfl; exact ⟨Embedding.ofIsEmpty⟩
    rintro ⟨e⟩
    exact isEmpty_coe_sort.1 e.toFun.isEmpty
  refine ⟨fun h ↦ ?_, fun ⟨e⟩ ↦ e.encard_le⟩
  obtain ⟨f, hst, hf⟩ := hs.exists_injOn_of_encard_le h
  exact ⟨codRestrict (s.restrict f) t (fun x ↦ by aesop), hf.injective.codRestrict _⟩

theorem Set.Finite.encard_le_iff_nonempty_embedding' {s : Set α} {t : Set β} (ht : t.Finite) :
    s.encard ≤ t.encard ↔ Nonempty (s ↪ t) := by
  obtain (hs | hs) := s.finite_or_infinite
  · exact hs.encard_le_iff_nonempty_embedding
  rw [hs.encard_eq, top_le_iff, encard_eq_top_iff, Set.Infinite, iff_true_intro ht,
    not_true, false_iff]
  rintro ⟨e⟩
  have hle := e.encard_le
  rw [hs.encard_eq, top_le_iff, encard_eq_top_iff] at hle
  exact hle ht

@[simp]
lemma finsum_mem_const {M : Type*} [AddCommMonoid M] (s : Set α) (a : M) :
    ∑ᶠ x ∈ s, a = s.ncard • a := by
  obtain hs | hs := s.finite_or_infinite
  · rw [finsum_mem_eq_finite_toFinset_sum _ hs, Finset.sum_const, ncard_eq_toFinset_card _ hs]
  obtain rfl | hne := eq_or_ne a 0
  · simp
  rw [hs.ncard, finsum_mem_eq_zero_of_infinite (by simpa [Function.support, hne]), zero_smul]

lemma finsum_one (s : Set α) : ∑ᶠ x ∈ s, 1 = s.ncard := by
  simp
  -- obtain hs | hs := s.finite_or_infinite
  -- · rw [finsum_mem_eq_finite_toFinset_sum _ hs, ncard_eq_toFinset_card _ hs]
  --   simp
  -- rw [hs.ncard, finsum_mem_eq_zero_of_infinite (by simpa [Function.support])]

lemma ENat.card_coe_setOf_ne (a : α) : ENat.card {i | i ≠ a} = ENat.card α - 1 := by
  rw [← encard_univ α, ENat.card_coe_set_eq, ← encard_diff_singleton_of_mem (mem_univ a)]
  convert rfl using 2
  ext
  simp
