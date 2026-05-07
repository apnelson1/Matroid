import Matroid.ForMathlib.Topology.Summable
import Mathlib.Topology.Instances.ENat
import Matroid.ForMathlib.ENat
import Matroid.ForMathlib.Card
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.Order

open Set Function

instance : AddEqTopClass ℕ∞ where
  eq_or_eq_of_add a b := by simp

namespace ENat


variable {ι : Sort*} {α β : Type*} {f g : α → ℕ∞} {s t : Set α}

protected theorem hasSum : HasSum f (⨆ s : Finset α, ∑ a ∈ s, f a) :=
  hasSum

@[simp] protected theorem summable : Summable f :=
  summable

protected theorem tsum_eq_iSup_sum : ∑' x, f x = (⨆ s : Finset α, ∑ a ∈ s, f a) :=
  tsum_eq_iSup_sum

protected theorem tsum_comm {f : α → β → ℕ∞} : ∑' (a) (b), f a b = ∑' (b) (a), f a b :=
  tsum_comm

protected theorem tsum_prod {f : α → β → ℕ∞} : ∑' p : α × β, f p.1 p.2 = ∑' (a) (b), f a b :=
  tsum_prod

protected theorem tsum_add : ∑' a, (f a + g a) = ∑' a, f a + ∑' a, g a :=
  tsum_add

protected theorem tsum_le_tsum (h : f ≤ g) : ∑' a, f a ≤ ∑' a, g a :=
  tsum_le_tsum h

protected theorem sum_le_tsum {f : α → ℕ∞} (s : Finset α) : ∑ x ∈ s, f x ≤ ∑' x, f x :=
  sum_le_tsum s

protected theorem le_tsum (a : α) : f a ≤ ∑' a, f a :=
  le_tsum a

protected theorem le_tsum_of_mem {s : Set α} {a : α} (ha : a ∈ s) : f a ≤ ∑' x : s, f x :=
  le_tsum_of_mem ha

@[simp] protected theorem tsum_eq_zero : ∑' i, f i = 0 ↔ ∀ i, f i = 0 :=
  tsum_eq_zero

protected theorem tsum_eq_top_of_eq_top : (∃ a, f a = ⊤) → ∑' a, f a = ⊤ :=
  tsum_eq_top_of_eq_top

protected theorem tsum_subtype_eq_top_of_eq_top {s : Set α} (h : ∃ a ∈ s, f a = ⊤) :
    ∑' a : s, f a = ⊤ :=
  tsum_subtype_eq_top_of_eq_top h

protected theorem tsum_union_disjoint {s t : Set α} (hd : Disjoint s t) :
    ∑' (x : ↑(s ∪ t)), f x = ∑' (x : s), f x + ∑' (x : t), f x :=
  tsum_union_disjoint hd

protected theorem tsum_le_of_subset {s t : Set α} (h : s ⊆ t) :
    ∑' (x : s), f x ≤ ∑' (x : t), f x :=
  tsum_le_of_subset h

protected theorem tsum_union_le (s t : Set α) :
    ∑' (x : ↑(s ∪ t)), f (x : α) ≤ ∑' (x : s), f x + ∑' (x : t), f x :=
  tsum_union_le ..

protected theorem tsum_insert {s : Set α} {a : α} (h : a ∉ s) :
    ∑' (x : ↑(insert a s)), f x = f a + ∑' (x : s), f x :=
  tsum_insert h

protected theorem tsum_singleton_add_tsum_ne {a : α} :
    f a + (∑' (x : {x // x ≠ a}), f x) = ∑' x, f x :=
  tsum_singleton_add_tsum_ne

protected theorem mul_tsum (c : ℕ∞) : c * ∑' a, f a = ∑' a, c * f a :=
  mul_tsum c f

protected theorem tsum_mul (c : ℕ∞) : (∑' a, f a) * c = ∑' a, f a * c :=
  tsum_mul c f

protected theorem tsum_comp_le_tsum_of_injective {f : α → β} (hf : Injective f) (g : β → ℕ∞) :
    ∑' x, g (f x) ≤ ∑' y, g y :=
  tsum_comp_le_tsum_of_injective hf g

protected theorem tsum_le_tsum_comp_of_surjective {f : α → β} (hf : Surjective f) (g : β → ℕ∞) :
    ∑' y, g y ≤ ∑' x, g (f x) :=
  tsum_le_tsum_comp_of_surjective hf g

protected theorem tsum_comp_eq_tsum_of_bijective {f : α → β} (hf : f.Bijective) (g : β → ℕ∞) :
    ∑' x, g (f x) = ∑' y, g y :=
  tsum_comp_eq_tsum_of_bijective hf g

protected theorem tsum_range_le_tsum_comp (f : β → ℕ∞) (g : α → β) :
    ∑' (x : range g), f x ≤ ∑' x, f (g x) :=
  tsum_range_le_tsum_comp f g

protected theorem tsum_comp_eq_tsum_of_equiv (e : α ≃ β) (g : β → ℕ∞) :
    ∑' x, g (e x) = ∑' y, g y :=
  tsum_comp_eq_tsum_of_equiv e g

protected theorem tsum_image_le_tsum_comp (f : β → ℕ∞) (g : α → β) (s : Set α) :
    ∑' x : (g '' s), f x ≤ ∑' x : s, f (g x) :=
  tsum_image_le_tsum_comp f g s

protected theorem tsum_mono_subtype (f : α → ℕ∞) {s t : Set α} (h : s ⊆ t) :
    ∑' x : s, f x ≤ ∑' x : t, f x :=
  tsum_mono_subtype f h

protected theorem tsum_sigma {β : α → Type*} (f : ∀ a, β a → ℕ∞) :
    ∑' p : Σa, β a, f p.1 p.2 = ∑' (a) (b), f a b :=
  tsum_sigma f

protected theorem tsum_sigma' {β : α → Type*} (f : (Σ a, β a) → ℕ∞) :
    ∑' p : Σ a, β a, f p = ∑' (a) (b), f ⟨a, b⟩ :=
  tsum_sigma' f

protected theorem tsum_eq_top_iff_of_finite (hs : s.Finite) :
    ∑' (x : s), f x = ⊤ ↔ ∃ a ∈ s, f a = ⊤ :=
  tsum_eq_top_iff_of_finite hs (by simp)

variable {ι : Type*}

protected theorem tsum_iUnion_le_tsum (f : α → ℕ∞) (t : ι → Set α) :
    ∑' x : ⋃ i, t i, f x ≤ ∑' i, ∑' x : (t i), f x :=
  tsum_iUnion_le_tsum ..

protected theorem tsum_biUnion_le_tsum (f : α → ℕ∞) (s : Set ι) (t : ι → Set α) :
    ∑' x : ⋃ i ∈ s , t i, f x ≤ ∑' i : s, ∑' x : t i, f x :=
  tsum_biUnion_le_tsum ..

protected theorem tsum_biUnion_le (f : α → ℕ∞) (s : Finset ι) (t : ι → Set α) :
    ∑' x : ⋃ i ∈ s, t i, f x ≤ ∑ i ∈ s, ∑' x : t i, f x :=
  tsum_biUnion_le ..

protected theorem tsum_iUnion_le_sum [Fintype ι] (f : α → ℕ∞) (t : ι → Set α) :
    ∑' x : ⋃ i, t i, f x ≤ ∑ i, ∑' x : t i, f x :=
  tsum_iUnion_le_sum f t

protected theorem tsum_iUnion_eq_tsum (f : α → ℕ∞) (t : ι → Set α) (ht : Pairwise (Disjoint on t)) :
    ∑' x : ⋃ i, t i, f x = ∑' i, ∑' x : t i, f x :=
  tsum_iUnion_eq_tsum _ _ ht

protected theorem tsum_subtype_eq_tsum_support (s : Set α) (f : α → ℕ∞) :
    ∑' (x : s), f x = ∑' (x : {i ∈ s | f i ≠ 0}), f x :=
  tsum_subtype_eq_tsum_support s f

protected theorem tsum_eq_top_of_support_infinite (hf : f.support.Infinite) : ∑' a, f a = ⊤ := by
  rw [ENat.tsum_eq_iSup_sum, iSup_eq_top]
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
  · rw [← tsum_subtype_support, ENat.tsum_eq_top_iff_of_finite hfin] at htop
    exact Exists.elim htop <| fun a h ↦ ⟨a, h.2⟩
  rw [← top_le_iff, ← ha]
  exact ENat.le_tsum a

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
  rw [← ENat.tsum_one s, ENat.mul_tsum, mul_one]

protected theorem tsum_subtype_const' (s : Set α) (c : ℕ∞) :
    ∑' (x : s), (fun (_ : α) ↦ c) x = c * s.encard := by
  rw [← ENat.tsum_one s, ENat.mul_tsum, mul_one]

protected theorem encard_support_le_tsum : f.support.encard ≤ ∑' x, f x := by
  classical
  rw [← ENat.tsum_one', tsum_subtype]
  refine ENat.tsum_le_tsum fun x ↦ ?_
  rw [indicator_apply]
  split_ifs with h
  · simpa [ENat.one_le_iff_ne_zero]
  simp

protected theorem tsum_ite_const {P : α → Prop} {s t : ℕ∞} [DecidablePred P] :
    ∑' x, (if P x then s else t) = s * {x | P x}.encard + t * {x | ¬ P x}.encard := by
  rw [tsum_ite, ENat.tsum_subtype_const, ENat.tsum_subtype_const]

protected theorem tsum_encard_eq_encard_iUnion {ι} {s : ι → Set α} (hI : Pairwise (Disjoint on s)) :
    ∑' i, (s i).encard = (⋃ i, s i).encard := by
  simp_rw [← ENat.tsum_one', ENat.tsum_iUnion_eq_tsum _ _ hI]

theorem encard_iUnion_le_tsum_encard {ι} {s : ι → Set α} :
    (⋃ i, s i).encard ≤ ∑' i, (s i).encard := by
  rw [← ENat.tsum_one]
  exact (ENat.tsum_iUnion_le_tsum 1 s).trans_eq <| by simp

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
  have h1 := ENat.tsum_insert (a := a) (s := t \ {a}) (f := fun i ↦ (s i).encard) (by simp)
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
