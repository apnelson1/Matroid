import Mathlib.Data.Set.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring
import Mathlib.Algebra.BigOperators.WithTop

open Set BigOperators

variable {α β : Type*} {s t : Set α} {n : ℕ}

theorem Finite.encard_union_eq_add_encard_iff_disjoint (h : (s ∪ t).Finite) :
    s.encard + t.encard = (s ∪ t).encard ↔ Disjoint s t := by
  rw [← add_zero (encard (s ∪ t)), ← encard_union_add_encard_inter, WithTop.add_left_cancel_iff
    h.encard_lt_top.ne, encard_eq_zero, disjoint_iff_inter_eq_empty]

@[simp] theorem encard_pair_le (e f : α) : encard {e,f} ≤ 2 := by
  obtain (rfl | hne) := eq_or_ne e f
  · simp only [mem_singleton_iff, insert_eq_of_mem, encard_singleton]; norm_num
  rw [encard_pair hne]

theorem Set.coe_le_encard_iff : n ≤ s.encard ↔ (s.Finite → n ≤ s.ncard) := by
  obtain (hfin | hinf) := s.finite_or_infinite
  · rw [← hfin.cast_ncard_eq, iff_true_intro hfin, Nat.cast_le, true_imp_iff]
  rw [hinf.encard_eq, iff_true_intro le_top, true_iff, iff_false_intro hinf, false_imp_iff]
  trivial

theorem Equiv.encard_univ_eq (e : α ≃ β) : encard (univ : Set α) = encard (univ : Set β) := by
  rw [encard_univ, encard_univ, PartENat.card_congr e]

theorem Equiv.encard_eq {s : Set α} {t : Set β} (e : s ≃ t) : s.encard = t.encard :=
  e.toEmbedding.enccard_le.antisymm e.symm.toEmbedding.enccard_le

theorem Fin.nonempty_embedding_iff_le_encard : Nonempty (Fin n ↪ s) ↔ n ≤ s.encard := by
  refine ⟨fun ⟨i⟩ ↦ ?_, fun h ↦ ?_⟩
  · convert ((Equiv.Set.univ (Fin n)).toEmbedding.trans i).enccard_le
    simp [encard_univ]
  obtain ⟨t, hts, hcard⟩ := exists_subset_encard_eq h
  have ht : t.Finite := finite_of_encard_eq_coe hcard
  rw [← ht.cast_ncard_eq, Nat.cast_inj, ncard_eq_toFinset_card t ht] at hcard
  refine ⟨(Finset.equivFinOfCardEq hcard).symm.toEmbedding.trans ?_ ⟩
  simp only [Finite.mem_toFinset]
  exact embeddingOfSubset t s hts

@[simp] theorem PartENat.card_option (α : Type*) :
    PartENat.card (Option α) = PartENat.card α + 1 := by
  obtain (hα | hα) := finite_or_infinite α
  · have _ := Fintype.ofFinite α; simp
  simp

theorem encard_iUnion {ι : Type*} [Fintype ι] (s : ι → Set α) (hs : univ.PairwiseDisjoint s) :
    encard (⋃ i, s i) = ∑ i, encard (s i) := by
  classical
  obtain (⟨i, hi⟩ | h) := em <| ∃ i, (s i).Infinite
  · rw [(hi.mono (subset_iUnion s i)).encard_eq]
    have hle := Finset.sum_le_sum_of_subset (f := fun i ↦ encard (s i)) (Finset.subset_univ {i})
    simp_rw [Finset.sum_singleton, hi.encard_eq, top_le_iff, eq_comm] at hle
    exact hle
  simp_rw [not_exists, not_infinite] at h
  rw [(finite_iUnion h).encard_eq_coe_toFinset_card]
  simp_rw [(h _).encard_eq_coe_toFinset_card]
  have h_eq := Finset.card_biUnion (s := Finset.univ) (t := fun i ↦ (h i).toFinset) ?_
  · convert congr_arg ((↑) : ℕ → ℕ∞) h_eq
    · ext x; simp
    simp only [Nat.cast_sum]
  simp only [Finset.mem_univ, ne_eq, Finite.disjoint_toFinset, forall_true_left]
  exact fun i j hij ↦ hs (mem_univ i) (mem_univ j) hij

theorem encard_biUnion {ι : Type*} {s : ι → Set α} (t : Finset ι)
    (ht : (t : Set ι).PairwiseDisjoint s) : encard (⋃ i ∈ t, s i) = ∑ i in t, encard (s i) := by
  convert encard_iUnion (fun i : t ↦ s i) ?_
  · ext x; simp
  · rw [Finset.univ_eq_attach, Finset.sum_attach _ (f := fun i ↦ (s i).encard)]
  rintro ⟨i, hi⟩ - ⟨j, hj⟩ - hne
  exact disjoint_iff_forall_ne.2 (ht hi hj (by simpa using hne)).ne_of_mem

theorem encard_iUnion_le {ι : Type*} [Fintype ι] (s : ι → Set α) :
    encard (⋃ i : ι, s i) ≤ ∑ i, encard (s i) := by
  classical
  obtain (⟨i, hi⟩ | h) := em <| ∃ i, (s i).Infinite
  · have hle := Finset.sum_le_sum_of_subset (f := fun i ↦ encard (s i)) (Finset.subset_univ {i})
    simp_rw [Finset.sum_singleton, hi.encard_eq] at hle
    exact le_top.trans hle
  simp_rw [not_exists, not_infinite] at h
  convert (Nat.cast_le (α := ℕ∞)).2
    (Finset.card_biUnion_le (s := Finset.univ) (t := fun i ↦ (h i).toFinset))
  · rw [(finite_iUnion h).encard_eq_coe_toFinset_card]
    congr
    ext x
    simp
  rw [Nat.cast_sum]
  exact Finset.sum_congr rfl (fun x _ ↦ (h x).encard_eq_coe_toFinset_card)

theorem encard_iUnion_eq_sum_iff_pairwiseDisjoint {ι : Type*} [Fintype ι] {s : ι → Set α}
    (hfin : ∀ i, (s i).Finite) :
    encard (⋃ i, s i) = ∑ i, encard (s i) ↔ univ.PairwiseDisjoint s := by
  classical
  refine ⟨fun hsum i _ j _ hij ↦ disjoint_iff_forall_ne.2 ?_, fun hdj ↦ encard_iUnion s hdj⟩
  rintro x hxi _ hxj rfl
  have hrw : ∀ t : Set α, encard t = encard (t \ {x}) + encard (t ∩ {x}) := by
    intro t
    rw [← encard_union_eq, diff_union_inter]
    exact disjoint_sdiff_left.mono_right inter_subset_right
  rw [hrw, Finset.sum_congr rfl (fun i _ ↦ hrw (s i)), Finset.sum_add_distrib,
    inter_eq_self_of_subset_right (singleton_subset_iff.2 (mem_iUnion_of_mem i hxi)),
    encard_singleton, eq_comm, iUnion_diff] at hsum

  have hlb := Finset.sum_le_sum_of_subset
    (f := fun i ↦ (s i ∩ {x}).encard) (Finset.subset_univ {i,j})
  simp_rw [Finset.sum_pair hij] at hlb
  rw [inter_eq_self_of_subset_right (by simpa), inter_eq_self_of_subset_right (by simpa),
    encard_singleton] at hlb
  have hcon := ((add_le_add_left hlb _).trans hsum.le).trans
    (add_le_add_right (encard_iUnion_le _) 1)
  rw [← add_assoc, WithTop.add_le_add_iff_right (by simp), ENat.add_one_le_iff] at hcon
  · exact hcon.ne rfl
  refine (WithTop.sum_lt_top (fun i _ ↦ ?_)).ne
  rw [encard_ne_top_iff]
  exact (hfin i).diff _

theorem encard_biUnion_eq_sum_iff_pairwiseDisjoint {ι : Type*} {u : Finset ι}
    {s : ι → Set α} (hs : ∀ i ∈ u, (s i).Finite) :
    encard (⋃ i ∈ u, s i) = ∑ i in u, encard (s i) ↔ (u : Set ι).PairwiseDisjoint s := by
  change encard (⋃ i ∈ (u : Set ι), _) = _ ↔ _
  rw [biUnion_eq_iUnion]
  convert encard_iUnion_eq_sum_iff_pairwiseDisjoint (ι := u) (s := fun i ↦ s i) (by simpa)
  · rw [Finset.univ_eq_attach, Finset.sum_attach _ (f := fun i ↦ encard (s i))]
  refine ⟨fun h i _ j _ hij ↦ h i.prop j.prop (by rwa [Ne, Subtype.coe_injective.eq_iff]),
    fun h i hi j hj hij ↦ ?_⟩
  exact h (mem_univ ⟨i, hi⟩) (mem_univ ⟨j,hj⟩) (by simpa)

theorem pairwiseDisjoint_of_encard_sum_le_encard_iUnion {ι : Type*} [Fintype ι] {s : ι → Set α}
    (hfin : ∀ i, (s i).Finite) (hle : ∑ i, encard (s i) ≤ encard (⋃ i, s i)) :
    univ.PairwiseDisjoint s := by
  rw [← encard_iUnion_eq_sum_iff_pairwiseDisjoint hfin, hle.antisymm (encard_iUnion_le s)]
