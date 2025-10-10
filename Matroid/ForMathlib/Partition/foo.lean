import Matroid.ForMathlib.Partition.Induce

variable {α : Type*} [CompleteLattice α] {P Q R : Partition α} {S T : Set α} {a b c : α}

namespace Partition

section foo

def foo (P : Partition α) (a : α) : α := P.cover a |>.supp

@[simp]
lemma foo_bot : foo P ⊥ = ⊥ := by
  simp [foo]

@[simp]
lemma foo_le_supp : foo P a ≤ P.supp := by
  simp only [foo, Partition.cover_supp, Partition.mem_parts, sSup_le_iff, Set.mem_setOf_eq, and_imp]
  exact fun _ hbP _ ↦ P.le_supp_of_mem hbP

lemma foo_le_of_le (haPb : a ⊓ P.supp ≤ b) (hbP : b ∈ P) : foo P a ≤ b := by
  simp only [foo, cover_supp, mem_parts, sSup_le_iff, Set.mem_setOf_eq, and_imp]
  refine fun x hxP hdj ↦ (P.eq_of_not_disjoint hxP hbP ?_).le
  contrapose! hdj
  refine disjoint_iff_inf_le.mpr <| hdj inf_le_right (le_trans ?_ haPb)
  exact inf_le_inf_left a <| le_supp_of_mem hxP

lemma subset_foo (hT : T ∈ P) : T ⊆ foo P S ↔ ¬ Disjoint S T := by
  simp only [foo, sUnion_image, not_disjoint_iff]
  refine ⟨fun h => ?_, fun ⟨x, hxS, hxT⟩ y hyT => ?_⟩
  · have := P.nonempty_of_mem hT
    obtain ⟨y, hyP, A, hAP, hA, hyA⟩ := by simpa using h this.some_mem
    obtain rfl := P.eq_of_mem_of_mem hAP hT hA this.some_mem
    use y, hyP, hyA
  simp only [mem_iUnion, mem_partOf_iff, exists_prop]
  use x, hxS
  rwa [rel_iff_right_mem_of_mem hT hyT]

lemma foo_eq_of_inter_subset (hS : (S ∩ P.supp).Nonempty) (hST : S ∩ P.supp ⊆ T) (hT : T ∈ P) :
    foo P S = T := by
  refine subset_antisymm (foo_subset_of_subset hST hT) <| (subset_foo hT).mpr ?_
  rw [not_disjoint_iff]
  use hS.some, hS.some_mem.1, hST hS.some_mem

@[simp]
lemma foo_eq_of_indiscrete' : (indiscrete' S).foo S = S := by
  obtain (h | h) := S.eq_empty_or_nonempty
  · subst S
    simp
  exact foo_eq_of_inter_subset (by simpa) (by simp) (by simp [h.ne_empty])

lemma inter_foo_eq_inter_supp : S ∩ foo P S = S ∩ P.supp := by
  ext x
  simp only [foo, sUnion_image, mem_inter_iff, mem_iUnion, mem_partOf_iff, exists_prop,
    and_congr_right_iff]
  exact fun hxS => ⟨fun ⟨y, hyS, hxy⟩ => hxy.left_mem, fun hx => ⟨x, hxS, rel_self_of_mem_supp hx⟩⟩

lemma self_subset_foo_iff : S ⊆ foo P S ↔ S ⊆ P.supp := by
  refine ⟨fun h x hxS => foo_subset_supp (h hxS), fun h => ?_⟩
  have : S = S ∩ P.supp := left_eq_inter.mpr h
  nth_rw 1 [this, ← inter_foo_eq_inter_supp]
  exact inter_subset_right

lemma foo_mem_iff : foo P S ∈ P ↔ (S ∩ P.supp).Nonempty ∧ ∃ T ∈ P, S ∩ P.supp ⊆ T := by
  refine ⟨fun h => ⟨?_, P.foo S, h, ?_⟩,
    fun ⟨hS, T, hTP, hST⟩ => foo_eq_of_inter_subset hS hST hTP ▸ hTP⟩
  · by_contra! hS
    rw [← disjoint_iff_inter_eq_empty, ← foo_eq_empty_iff] at hS
    simpa [hS] using P.nonempty_of_mem h
  rw [← inter_foo_eq_inter_supp]
  exact inter_subset_right

lemma subset_foo_of_le (hPQ : P ≤ Q) (hS : S ∈ P) : S ⊆ foo Q S := by
  rintro x hxS
  simp only [foo, sUnion_image, mem_iUnion, mem_partOf_iff, exists_prop]
  exact ⟨x, hxS, rel_le_of_le hPQ x x ⟨S, hS, hxS, hxS⟩⟩

lemma foo_mem_of_le (hPQ : P ≤ Q) (hS : S ∈ P) : foo Q S ∈ Q := by
  rw [foo_mem_iff]
  obtain ⟨T, hTQ, hST⟩ := hPQ S hS
  have : S ∩ Q.supp = S := inter_eq_left.mpr <| subset_trans hST (subset_of_mem hTQ)
  simp only [this, P.nonempty_of_mem hS, true_and]
  exact hPQ S hS

lemma foo_eq_self_of_le (hS : S ∈ Q) (hPQ : P ≤ Q) (hSP : S ⊆ P.supp) : foo P S = S := by
  ext a
  simp only [foo, sUnion_image, mem_iUnion, mem_partOf_iff, exists_prop]
  exact ⟨fun ⟨b, hbS, hab⟩ => (Rel.forall (rel_le_of_le hPQ a b hab) hS).mpr hbS,
    fun haS => ⟨a, haS, rel_self_iff_mem_supp.mpr (hSP haS)⟩⟩

lemma foo_eq_self_of_subset (hPQ : P ⊆ Q) (hS : S ∈ P) : foo Q S = S :=
  Q.eq_of_mem_of_mem (foo_mem_of_le (le_of_subset hPQ) hS) (hPQ hS)
    (self_subset_foo_iff.mpr ((P.subset_of_mem hS).trans <| supp_le_of_subset hPQ)
      (P.nonempty_of_mem hS).some_mem) (P.nonempty_of_mem hS).some_mem

@[simp]
lemma foo_eq_self_of_mem (hS : S ∈ P) : foo P S = S :=
  foo_eq_self_of_subset (subset_refl P) hS

lemma foo_subset_foo_foo (hPQ : P ≤ Q) : foo Q (foo P S) ⊆ foo Q S := by
  intro a
  simp only [foo, sUnion_image, mem_iUnion, mem_partOf_iff, exists_prop, iUnion_exists,
    biUnion_and', forall_exists_index, and_imp]
  exact fun b hbS c hPcb hQac ↦ ⟨b, hbS, hQac.trans (rel_le_of_le hPQ _ _ hPcb)⟩

lemma foo_foo_eq_foo (hPQ : P ≤ Q) (hS : S ⊆ P.supp) : foo Q (foo P S) = foo Q S := by
  refine subset_antisymm (foo_subset_foo_foo hPQ) fun a ↦ ?_
  simp only [foo, sUnion_image, mem_iUnion, mem_partOf_iff, exists_prop, iUnion_exists,
    biUnion_and', forall_exists_index, and_imp]
  intro b hbS hQab
  use b, hbS, b, rel_self_of_mem_supp (hS hbS)

end foo

@[simp]
lemma foo_eq_bot_iff : foo P a = ⊥ ↔ Disjoint a P.supp := by
  simp only [foo, cover_supp, mem_parts, sSup_eq_bot, Set.mem_setOf_eq, and_imp]
