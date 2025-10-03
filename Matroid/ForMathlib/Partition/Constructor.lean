import Matroid.ForMathlib.Partition.Lattice

open Set Function Relation

variable {α β ι ι' : Type*} {r : α → α → Prop} {f : ι → α} {x y z : α} {A B : Set α}



lemma Set.left_nonempty_of_not_disjoint {s t : Set α} (h : ¬ Disjoint s t) : s.Nonempty := by
  obtain ⟨u, hu, hsu⟩ := not_disjoint_iff.mp h
  use u

lemma Set.right_nonempty_of_not_disjoint {s t : Set α} (h : ¬ Disjoint s t) : t.Nonempty := by
  obtain ⟨u, hu, htu⟩ := not_disjoint_iff.mp h
  use u

namespace Partition

variable {s t u : Set α} {S T : Set (Set α)} {P Q : Partition (Set α)}


def mk' (S : Set (Set α)) : Partition (Set α) := ⨆ s ∈ S, Partition.indiscrete' s

lemma mk'_agree (hS : S.PairwiseDisjoint id) : S.Pairwise (Agree on indiscrete') := by
  rintro x hx y hy hxy
  rw [agree_on_indiscrete'_iff]
  right
  exact hS hx hy hxy

lemma IsPartition.mk'_agree (hS : IsPartition S) : S.Pairwise (Agree on indiscrete') := by
  obtain ⟨P, hP⟩ := hS
  exact hP ▸ Partition.mk'_agree P.indep.pairwiseDisjoint

@[simp]
lemma mk'_parts_bot_not_mem (hS : S.PairwiseDisjoint id) (hSbot : ∅ ∉ S) : (mk' S).parts = S := by
  rw [mk', biSup_parts_of_agree (mk'_agree hS)]
  ext s
  have : s ∈ S → s ≠ ∅ := (ne_of_mem_of_not_mem · hSbot)
  simpa

@[simp]
lemma mk'_parts (hS : S.PairwiseDisjoint id) : (mk' S).parts = S \ {⊥} := by
  rw [mk', biSup_parts_of_agree (mk'_agree hS)]
  ext s
  simp [and_comm]

lemma IsPartition.mk'_parts (hS : IsPartition S) : (mk' S).parts = S := by
  obtain ⟨P, hP⟩ := hS
  exact hP ▸ mk'_parts_bot_not_mem P.indep.pairwiseDisjoint P.bot_not_mem

lemma mk'_parts_iff : (mk' S).parts = S ↔ IsPartition S :=
  ⟨fun hS ↦ ⟨mk' S, hS⟩, IsPartition.mk'_parts⟩

@[simp]
lemma mem_mk'_iff (hS : S.PairwiseDisjoint id) : s ∈ mk' S ↔ s ≠ ⊥ ∧ s ∈ S := by
  rw [← mem_parts, mk'_parts hS]
  simp [and_comm]

@[simp↓]
lemma IsPartition.mem_mk'_iff (hS : IsPartition S) : s ∈ mk' S ↔ s ∈ S := by
  rw [← mem_parts, hS.mk'_parts]

lemma mk'_exists_subset_of_mem (hs : s ∈ S) (hs' : s.Nonempty) : ∃ t ∈ mk' S, s ⊆ t := by
  suffices indiscrete' s ≤ mk' S by exact this s (by simp [hs'.ne_empty])
  exact le_biSup _ hs

lemma mk'_exists_unique_subset_of_mem (hs : s ∈ S) (hs' : s.Nonempty) : ∃! t ∈ mk' S, s ⊆ t := by
  obtain ⟨t, ht, hst⟩ := mk'_exists_subset_of_mem hs hs'
  obtain ⟨a, has⟩ := hs'
  exact ⟨t, ⟨ht, hst⟩, fun u ⟨hu, hsu⟩ => eq_of_mem_of_mem hu ht (hsu has) (hst has)⟩

lemma mk'_exists_unique_not_disjoint_of_mem (hs : s ∈ S) (hs' : s.Nonempty) :
    ∃! t ∈ mk' S, ¬ Disjoint s t := by
  simp_rw [not_disjoint_iff]
  obtain ⟨t, ⟨ht'S, hst⟩, heqt⟩ := mk'_exists_unique_subset_of_mem hs hs'
  exact ⟨t, ⟨ht'S, ⟨hs'.some, hs'.some_mem, hst hs'.some_mem⟩⟩,
    fun w ⟨hw'S, a, has, haw⟩ => eq_of_mem_of_mem hw'S ht'S haw (hst has)⟩

@[simp]
lemma mk'_supp : (mk' S).supp = ⋃₀ S := by
  ext x
  simp [mk']

lemma indiscrete'_le_mk' (has : s ∈ S) : Partition.indiscrete' s ≤ mk' S :=
  le_biSup indiscrete' has

lemma mk'_mono (hS : S ⊆ T) : mk' S ≤ mk' T :=
  biSup_mono hS

lemma exists_subset_parts_iff_nonempty_and_eq_or_disjoint :
    IsPartition S ↔ ∅ ∉ S ∧ S.PairwiseDisjoint id :=
  ⟨fun hS ↦ ⟨fun a ↦ hS.bot_not_mem a, hS.pairwiseDisjoint⟩,
    fun ⟨hS, hSdj⟩ => ⟨ofPairwiseDisjoint hSdj, by simp [hS]⟩⟩

lemma exists_parts_eq_pair_iff_nonempty_and_eq_or_disjoint {a b  : Set α} :
    IsPartition {a, b} ↔ a.Nonempty ∧ b.Nonempty ∧ (a = b ∨ Disjoint a b) := by
  rw [exists_subset_parts_iff_nonempty_and_eq_or_disjoint, pairwiseDisjoint_pair_iff, ← and_assoc]
  exact and_congr_left <| by simp [eq_comm, nonempty_iff_ne_empty]

lemma mk'_foo_mem (hs : s ∈ S) (hs' : s.Nonempty) : foo (mk' S) s ∈ mk' S :=
  foo_mem_of_le (le_biSup _ hs) <| by simp [hs'.ne_empty]

@[simp]
lemma mk'_foo_mem_iff (hs : s ∈ S) : foo (mk' S) s ∈ mk' S ↔ s.Nonempty := by
  refine ⟨fun h => ?_, mk'_foo_mem hs⟩
  by_contra! heq
  subst s
  rw [foo_empty] at h
  exact (mk' S).bot_not_mem h

lemma subset_mk'_foo (hs : s ∈ S) (hs' : s.Nonempty) : s ⊆ foo (mk' S) s :=
  subset_foo_of_le (le_biSup _ hs) <| by simp [hs'.ne_empty]

lemma eq_mk'_foo_of_mem (hs : s ∈ S) (ht : t ∈ mk' S) (hst : ¬ Disjoint s t) :
    foo (mk' S) s = t := by
  have hs' : s.Nonempty := left_nonempty_of_not_disjoint hst
  obtain ⟨u, hu, hsu⟩ := mk'_exists_unique_not_disjoint_of_mem hs hs'
  obtain rfl := hsu t ⟨ht, hst⟩
  refine hsu (foo (mk' S) s) ⟨mk'_foo_mem hs hs', ?_⟩
  exact not_disjoint_iff.mpr ⟨hs'.some, hs'.some_mem, subset_mk'_foo hs hs' hs'.some_mem⟩

lemma mk'_foo_eq_of_not_disjoint (hs : s ∈ S) (ht : t ∈ S) (hdisj : ¬ Disjoint s t) :
    foo (mk' S) s = foo (mk' S) t := by
  have htne : t.Nonempty := right_nonempty_of_not_disjoint hdisj
  apply eq_mk'_foo_of_mem hs <| mk'_foo_mem ht htne
  contrapose! hdisj
  exact hdisj.mono_right <| subset_mk'_foo ht htne

@[simp]
lemma mk'_singleton (s : Set α) : mk' {s} = Partition.indiscrete' s :=
  ext fun x => by aesop

@[simp]
lemma mk'_insert (s : Set α) (S : Set (Set α)) :
    mk' (insert s S) = mk' S ⊔ Partition.indiscrete' s := by
  ext x y
  rw [mk', mk', iSup_insert, sup_comm]

lemma foo_mk'_surjOn : SurjOn (foo (mk' S)) S (mk' S).parts := by
  intro s hs
  obtain ⟨a, has⟩ := (mk' S).nonempty_of_mem hs
  obtain ⟨t, htS, hst⟩ := by simpa using le_supp_of_mem hs has
  use t, htS, eq_mk'_foo_of_mem htS hs (not_disjoint_iff.mpr (by use a))

lemma foo_mk'_injOn_iff : S.InjOn (foo (mk' S)) ↔ S.EqOn (foo (mk' S)) id := by
  refine ⟨fun h s hsS => ?_, fun h s hsS t htS heq => by rwa [h hsS, h htS] at heq⟩
  apply subset_antisymm ?_
  · refine self_subset_foo_iff.mpr <| mk'_supp ▸ ?_
    exact subset_sUnion_of_subset S s subset_rfl hsS
  by_contra! hsu
  obtain ⟨a, hafx, hax⟩ := not_subset_iff_exists_mem_notMem.mp hsu; clear hsu
  obtain (rfl | hsnem) := eq_empty_or_nonempty s
  · simp at hafx
  have hsmem := mk'_foo_mem hsS hsnem
  obtain ⟨t, htS, hzt⟩ := by simpa using le_supp_of_mem hsmem hafx
  obtain rfl := h hsS htS (eq_mk'_foo_of_mem htS hsmem <| not_disjoint_iff.mpr (by use a)).symm
  exact hax hzt

lemma mk'_pair_nontrivial_iff :
    (mk' {s, t}).parts.Nontrivial ↔ (mk' {s, t}).parts = {s, t} ∧ s ≠ t := by
  refine ⟨fun ⟨x, hx, y, hy, hne⟩ => ?_, fun h => h.1.symm ▸ nontrivial_pair h.2⟩
  obtain ⟨u, huS, rfl⟩ := foo_mk'_surjOn hx
  obtain ⟨v, hvS, rfl⟩ := foo_mk'_surjOn hy
  obtain (rfl | rfl) := (by simpa using huS) <;> obtain (rfl | rfl) := by simpa using hvS
  on_goal 4 => simp at hne
  on_goal 1 => simp at hne
  all_goals
  · rw [mem_parts, mk'_foo_mem_iff (by simp)] at hx hy
    have hdisj := not_imp_comm.mp (mk'_foo_eq_of_not_disjoint huS hvS) hne
    refine ⟨(mk'_parts_bot_not_mem (pairwiseDisjoint_pair (by simp [onFun, hdisj, disjoint_comm]))
      ?_), ?_⟩ <;> simp [hdisj.ne hx.ne_empty, ne_comm, hx.ne_empty.symm, hy.ne_empty.symm]
