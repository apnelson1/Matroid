import Matroid.ForMathlib.Topology.Summable
import Mathlib.Topology.Instances.ENat
import Matroid.ForMathlib.ENat
import Matroid.ForMathlib.Card
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Order

open Set Function

instance : AddEqTopClass ℕ∞ := inferInstanceAs <| AddEqTopClass (WithTop ℕ)

instance : IsQuantale ℕ∞ where
  mul_sSup_distrib _ _ := ENat.mul_sSup ..
  sSup_mul_distrib _ _ := ENat.sSup_mul ..

namespace ENat

variable {ι : Type*} {α β : Type*} {f g : α → ℕ∞} {s t : Set α}

protected theorem tsum_eq_top_of_support_infinite (hf : f.support.Infinite) : ∑' a, f a = ⊤ := by
  rw [tsum_eq_iSup_sum, iSup_eq_top]
  intro b hb
  lift b to ℕ using hb.ne
  obtain ⟨t, htf, hbt, hfin⟩ := hf.exists_finite_subset_encard_gt b
  refine ⟨hfin.toFinset, hbt.trans_le ?_⟩
  rw [hfin.encard_eq_coe_toFinset_card, Finset.card_eq_sum_ones, Nat.cast_sum]
  refine Finset.sum_le_sum fun i hi ↦ ?_
  simp only [Nat.cast_one, ENat.one_le_iff_ne_zero]
  exact htf <| by simpa using hi

protected theorem tsum_const_eq_top {ι : Type*} [Infinite ι] {c : ℕ∞} (hc : c ≠ 0) :
    ∑' (_ : ι), c = ⊤ :=
  ENat.tsum_eq_top_of_support_infinite <| by rwa [Function.support_const hc, infinite_univ_iff]

protected theorem tsum_eq_top_iff : ∑' a, f a = ⊤ ↔ f.support.Infinite ∨ ∃ a, f a = ⊤ := by
  rw [iff_def, or_imp, and_iff_right ENat.tsum_eq_top_of_support_infinite, or_iff_not_imp_left,
    not_infinite]
  refine ⟨fun htop hfin ↦ ?_, fun ⟨a, ha⟩ ↦ ?_⟩
  · rw [← tsum_subtype_support, tsum_eq_top_iff_of_finite hfin] at htop
    exact Exists.elim htop <| fun a h ↦ ⟨a, h.2⟩
  rw [← top_le_iff, ← ha]
  exact le_tsum a

protected theorem tsum_subtype_eq_top_iff {s : Set α} :
    ∑' (a : s), f a = ⊤ ↔ (s ∩ f.support).Infinite ∨ ∃ a ∈ s, f a = ⊤ := by
  simp only [ENat.tsum_eq_top_iff, Subtype.exists, exists_prop]
  convert Iff.rfl
  convert Set.finite_image_iff Subtype.val_injective.injOn
  aesop

protected theorem tsum_subtype_eq_top_of_inter_support_infinite {s : Set α}
    (hf : (s ∩ f.support).Infinite) : ∑' (a : s), f a = ⊤ :=
  ENat.tsum_subtype_eq_top_iff.2 <| Or.inl hf

protected theorem tsum_subtype_const_eq_top_of_ne_zero {s : Set α} (hs : s.Infinite) {c : ℕ∞}
    (hc : c ≠ 0) : ∑' (_ : s), c = ⊤ :=
  ENat.tsum_subtype_eq_top_of_inter_support_infinite <| by rwa [support_const hc, inter_univ]

section Card

@[simp] protected theorem tsum_const (c : ℕ∞) : ∑' _ : ι, c = c * ENat.card ι := by
  obtain hι | hι := finite_or_infinite ι
  · have := Fintype.ofFinite ι
    simp [mul_comm]
  obtain rfl | hne := eq_or_ne c 0
  · simp
  rw [ENat.tsum_eq_top_of_support_infinite, card_eq_top_of_infinite, mul_top hne]
  rwa [support_const hne, infinite_univ_iff]

/-- A version of `ENat.tsum_one` where the `1` is explicitly a function from the type rather than
  from the subtype. Useful for rewriting. -/
protected theorem tsum_one' (s : Set α) : ∑' (i : s), (1 : α → ℕ∞) i = s.encard := by
  simp only [Pi.one_apply, ENat.tsum_const, card_coe_set_eq, one_mul]

@[simp] protected theorem tsum_one (s : Set α) : ∑' (_ : s), 1 = s.encard :=
  ENat.tsum_one' s

@[simp] protected theorem tsum_subtype_const (s : Set α) (c : ℕ∞) :
    ∑' (_ : s), c = c * s.encard := by
  rw [← ENat.tsum_one s, mul_tsum, mul_one]

protected theorem tsum_subtype_const' (s : Set α) (c : ℕ∞) :
    ∑' (x : s), (fun (_ : α) ↦ c) x = c * s.encard := by
  rw [← ENat.tsum_one s, mul_tsum, mul_one]

protected theorem encard_support_le_tsum : f.support.encard ≤ ∑' x, f x := by
  classical
  rw [← ENat.tsum_one', tsum_subtype]
  refine tsum_le_tsum fun x ↦ ?_
  rw [indicator_apply]
  split_ifs with h
  · simpa [ENat.one_le_iff_ne_zero]
  simp

protected theorem tsum_ite_const {P : α → Prop} {s t : ℕ∞} [DecidablePred P] :
    ∑' x, (if P x then s else t) = s * {x | P x}.encard + t * {x | ¬ P x}.encard := by
  rw [tsum_ite, ENat.tsum_subtype_const, ENat.tsum_subtype_const]

protected theorem tsum_encard_eq_encard_iUnion {ι} {s : ι → Set α} (hI : Pairwise (Disjoint on s)) :
    ∑' i, (s i).encard = (⋃ i, s i).encard := by
  simp_rw [← ENat.tsum_one', tsum_iUnion_eq_tsum _ _ hI]

theorem encard_iUnion_le_tsum_encard {ι} {s : ι → Set α} :
    (⋃ i, s i).encard ≤ ∑' i, (s i).encard := by
  rw [← ENat.tsum_one]
  exact (tsum_iUnion_le_tsum 1 s).trans_eq <| by simp

theorem tsum_encard_eq_encard_biUnion {ι} {s : ι → Set α} {t : Set ι}
    (hI : t.PairwiseDisjoint s) : ∑' i : t, (s i).encard = (⋃ i ∈ t, s i).encard := by
  rw [biUnion_eq_iUnion, ← ENat.tsum_encard_eq_encard_iUnion]
  simp_rw [Pairwise, Disjoint]
  aesop

theorem encard_biUnion_le_tsum_encard {ι} {s : ι → Set α} {I : Set ι} :
    (⋃ i ∈ I, s i).encard ≤ ∑' i : I, (s i).encard := by
  rw [biUnion_eq_iUnion]
  apply encard_iUnion_le_tsum_encard

protected theorem encard_eq_tsum_ite (s : Set α) [DecidablePred (· ∈ s)] :
    s.encard = ∑' (x : α), if x ∈ s then 1 else 0 := by
  nth_rw 1 [← inter_univ s, ← iUnion_of_singleton α, inter_iUnion,
    ← ENat.tsum_encard_eq_encard_iUnion (by simp +contextual [Pairwise, disjoint_left]), tsum_congr]
  intro b
  split_ifs with hb
  · rw [inter_eq_self_of_subset_right (by simpa), encard_singleton]
  rw [inter_singleton_eq_empty.2 hb, encard_empty]

theorem tsum_encard_eq_encard_biUnion_iff {ι} {s : ι → Set α} {t : Set ι}
    (hfin : (⋃ i ∈ t, s i).Finite) :
    ∑' i : t, (s i).encard = (⋃ i ∈ t, s i).encard ↔ t.PairwiseDisjoint s := by
  refine ⟨fun h ↦ ?_, tsum_encard_eq_encard_biUnion⟩
  by_contra hndj
  simp only [PairwiseDisjoint, Set.Pairwise, ne_eq, onFun, disjoint_left, not_forall, not_not,
    exists_prop] at hndj
  obtain ⟨a, ha, b, hb, hab, x, hxa, hxb⟩ := hndj
  have h1 := tsum_insert (a := a) (s := t \ {a}) (f := fun i ↦ (s i).encard) (by simp)
  rw [tsum_congr_set_coe (insert_diff_self_of_mem ha) (f := fun i ↦ (s i).encard), h] at h1
  have h2 := biUnion_insert a (t \ {a}) s
  rw [insert_diff_self_of_mem ha] at h2
  simp only at h1
  have hle := add_le_add_right (encard_biUnion_le_tsum_encard (s := s) (I := t \ {a})) (s a).encard
  rw [← h1, ← encard_union_add_encard_inter, h2, ENat.add_le_left_iff, encard_eq_top_iff,
    encard_eq_zero, ← disjoint_iff_inter_eq_empty, disjoint_left, ← h2,
    or_iff_right hfin.not_infinite] at hle
  simp only [mem_diff, mem_singleton_iff, mem_iUnion, exists_prop, not_exists, not_and,
    and_imp, not_imp_not] at hle
  exact hab (hle hxa b hb hxb).symm

theorem tsum_encard_eq_encard_iUnion_iff {ι} {s : ι → Set α} (hfin : (⋃ i, s i).Finite) :
    ∑' i, (s i).encard = (⋃ i, s i).encard ↔ Pairwise (Disjoint on s) := by
  rw [← tsum_univ, ← biUnion_univ, tsum_encard_eq_encard_biUnion_iff (by simpa)]
  rw [PairwiseDisjoint, pairwise_univ]

protected theorem tsum_encard_eq_encard_sUnion {c : Set (Set α)} (hc : c.PairwiseDisjoint id) :
    ∑' (t : c), (t : Set α).encard = (⋃₀ c).encard := by
  rw [sUnion_eq_iUnion, ← ENat.tsum_encard_eq_encard_iUnion]
  rintro ⟨i,hi⟩ ⟨j,hj⟩ hij
  exact hc hi hj (by simpa using hij)

theorem encard_sUnion_le_tsum_encard {c : Set (Set α)} : (⋃₀ c).encard ≤ ∑' s : c, s.1.encard := by
  rw [sUnion_eq_iUnion]
  apply encard_iUnion_le_tsum_encard

protected theorem tsum_inter_fiber_eq {ι} {s : Set ι} (f : ι → α) :
    ∑' (a : α), (s ∩ f ⁻¹' {a}).encard = s.encard := by
  rw [ENat.tsum_encard_eq_encard_iUnion]
  · congr
    aesop
  refine fun i j hij ↦ disjoint_iff_forall_ne.2 ?_
  rintro a ⟨-,rfl⟩ _ ⟨-,rfl⟩ rfl
  exact hij rfl

protected theorem tsum_fiber_eq {ι} (f : ι → α) :
    ∑' (a : α), (f ⁻¹' {a}).encard = (univ : Set ι).encard := by
  rw [← ENat.tsum_inter_fiber_eq (s := univ) f, tsum_congr]
  simp

end Card

end ENat
