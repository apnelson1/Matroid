import Mathlib.Topology.Instances.ENat
import Mathlib.Data.ENat.Lattice
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.Order.T5
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Order.Monotone
import Mathlib.Tactic.ENatToNat
import Mathlib.Data.Set.Card
import Matroid.ForMathlib.ENat
import Matroid.ForMathlib.Card
import Mathlib.Algebra.Group.Pointwise.Finset.BigOperators

open Set Set.Notation Function

namespace ENat



variable {ι : Sort*}

instance : OrderTopology ℕ∞ := ⟨rfl⟩

variable {α β : Type*} {f g : α → ℕ∞} {s t : Set α}

protected theorem hasSum : HasSum f (⨆ s : Finset α, ∑ a ∈ s, f a) :=
  tendsto_atTop_iSup fun _ _ ↦ Finset.sum_le_sum_of_subset

@[simp] protected theorem summable : Summable f :=
  ⟨_, ENat.hasSum⟩

protected theorem tsum_eq_iSup_sum : ∑' x, f x = (⨆ s : Finset α, ∑ a ∈ s, f a) :=
  ENat.hasSum.tsum_eq

protected theorem tsum_comm {f : α → β → ℕ∞} : ∑' (a) (b), f a b = ∑' (b) (a), f a b :=
  ENat.summable.tsum_comm' (fun _ ↦ ENat.summable) fun _ ↦ ENat.summable

protected theorem tsum_prod {f : α → β → ℕ∞} : ∑' p : α × β, f p.1 p.2 = ∑' (a) (b), f a b :=
  ENat.summable.tsum_prod' fun _ ↦ ENat.summable

protected theorem tsum_add : ∑' a, (f a + g a) = ∑' a, f a + ∑' a, g a :=
  ENat.summable.tsum_add ENat.summable

protected theorem tsum_le_tsum (h : f ≤ g) : ∑' a, f a ≤ ∑' a, g a :=
  ENat.summable.tsum_le_tsum h ENat.summable

protected theorem sum_le_tsum {f : α → ℕ∞} (s : Finset α) : ∑ x ∈ s, f x ≤ ∑' x, f x :=
  ENat.summable.sum_le_tsum s (fun _ _ ↦ zero_le _)

protected theorem le_tsum (a : α) : f a ≤ ∑' a, f a :=
  ENat.summable.le_tsum' a

protected theorem le_tsum_of_mem {s : Set α} {a : α} (ha : a ∈ s) : f a ≤ ∑' x : s, f x :=
  ENat.le_tsum (⟨a,ha⟩ : s)

@[simp] protected theorem tsum_eq_zero : ∑' i, f i = 0 ↔ ∀ i, f i = 0 :=
  ENat.summable.tsum_eq_zero_iff

protected theorem tsum_eq_top_of_eq_top : (∃ a, f a = ⊤) → ∑' a, f a = ⊤
  | ⟨a, ha⟩ => top_unique <| ha ▸ ENat.le_tsum a

protected theorem tsum_subtype_eq_top_of_eq_top {s : Set α} (h : ∃ a ∈ s, f a = ⊤) :
    ∑' a : s, f a = ⊤ :=
  let ⟨a, ha, has⟩ := h
  ENat.tsum_eq_top_of_eq_top ⟨⟨a, ha⟩, has⟩

protected theorem tsum_union_disjoint {s t : Set α} (hd : Disjoint s t) :
    ∑' (x : ↑(s ∪ t)), f x = ∑' (x : s), f x + ∑' (x : t), f x :=
  ENat.summable.tsum_union_disjoint hd ENat.summable

protected theorem tsum_le_of_subset {s t : Set α} (h : s ⊆ t) :
    ∑' (x : s), f x ≤ ∑' (x : t), f x := by
  rw [← diff_union_of_subset h, ENat.tsum_union_disjoint disjoint_sdiff_left]
  exact le_add_self

protected theorem tsum_union_le (s t : Set α) :
    ∑' (x : ↑(s ∪ t)), f (x : α) ≤ ∑' (x : s), f x + ∑' (x : t), f x := by
  rw [← diff_union_self, ENat.tsum_union_disjoint disjoint_sdiff_left]
  exact add_le_add_right (ENat.tsum_le_of_subset diff_subset) _

protected theorem tsum_insert {s : Set α} {a : α} (h : a ∉ s) :
    ∑' (x : ↑(insert a s)), f x = f a + ∑' (x : s), f x := by
  rw [← singleton_union, ENat.tsum_union_disjoint, tsum_singleton]
  rwa [disjoint_singleton_left]

protected theorem tsum_sub (hfin : ∑' a, g a ≠ ⊤) (h : g ≤ f) :
    ∑' a, (f a - g a) = ∑' a, f a - ∑' a, g a := by
  rw [← WithTop.add_right_inj hfin, ← ENat.tsum_add,
    tsum_congr (fun i ↦ tsub_add_cancel_of_le (h i)), tsub_add_cancel_of_le (ENat.tsum_le_tsum h)]

protected theorem mul_tsum (c : ℕ∞) : c * ∑' a, f a = ∑' a, c * f a := by
  simp_rw [ENat.tsum_eq_iSup_sum, ENat.mul_iSup, Finset.mul_sum]

protected theorem tsum_mul (c : ℕ∞) : (∑' a, f a) * c = ∑' a, f a * c := by
  simp_rw [ENat.tsum_eq_iSup_sum, ENat.iSup_mul, Finset.sum_mul]

protected theorem tsum_eq_top_iff_of_finite (hs : s.Finite) :
    ∑' (x : s), f x = ⊤ ↔ ∃ a ∈ s, f a = ⊤ := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp
  | @insert a s₀ has₀ hs₀ ih => simp [ENat.tsum_insert has₀, ih]

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
  ENat.tsum_subtype_eq_top_of_inter_support_infinite (f := fun _ ↦ c)
    <| by rwa [support_const hc, inter_univ]

protected theorem tsum_comp_le_tsum_of_injective {f : α → β} (hf : Injective f) (g : β → ℕ∞) :
    ∑' x, g (f x) ≤ ∑' y, g y :=
  ENat.summable.tsum_le_tsum_of_inj f hf (fun _ _ ↦ zero_le _) (fun _ ↦ le_rfl) ENat.summable

protected theorem tsum_le_tsum_comp_of_surjective {f : α → β} (hf : Surjective f) (g : β → ℕ∞) :
    ∑' y, g y ≤ ∑' x, g (f x) :=
  calc ∑' y, g y = ∑' y, g (f (surjInv hf y)) := by simp only [surjInv_eq hf]
    _ ≤ ∑' x, g (f x) := ENat.tsum_comp_le_tsum_of_injective (injective_surjInv hf) _

protected theorem tsum_comp_eq_tsum_of_bijective {f : α → β} (hf : f.Bijective) (g : β → ℕ∞) :
    ∑' x, g (f x) = ∑' y, g y :=
  (ENat.tsum_comp_le_tsum_of_injective hf.injective g).antisymm
    (ENat.tsum_le_tsum_comp_of_surjective hf.surjective g)

protected theorem tsum_comp_eq_tsum_of_equiv (e : α ≃ β) (g : β → ℕ∞) :
    ∑' x, g (e x) = ∑' y, g y := by
  rw [ENat.tsum_comp_eq_tsum_of_bijective e.bijective]

protected theorem tsum_mono_subtype (f : α → ℕ∞) {s t : Set α} (h : s ⊆ t) :
    ∑' x : s, f x ≤ ∑' x : t, f x :=
  ENat.tsum_comp_le_tsum_of_injective (inclusion_injective h) _

protected theorem tsum_sigma {β : α → Type*} (f : ∀ a, β a → ℕ∞) :
    ∑' p : Σa, β a, f p.1 p.2 = ∑' (a) (b), f a b :=
  ENat.summable.tsum_sigma' (fun _ ↦ ENat.summable)

protected theorem tsum_sigma' {β : α → Type*} (f : (Σ a, β a) → ℕ∞) :
    ∑' p : Σ a, β a, f p = ∑' (a) (b), f ⟨a, b⟩ :=
  ENat.summable.tsum_sigma' (fun _ ↦ ENat.summable)

variable {ι : Type*}

protected theorem tsum_iUnion_le_tsum (f : α → ℕ∞) (t : ι → Set α) :
    ∑' x : ⋃ i, t i, f x ≤ ∑' i, ∑' x : (t i), f x :=
  calc ∑' x : ⋃ i, t i, f x ≤ ∑' x : Σ i, t i, f x.2 :=
    ENat.tsum_le_tsum_comp_of_surjective (sigmaToiUnion_surjective t) _
  _ = ∑' i, ∑' x : t i, f x := ENat.tsum_sigma' _

protected theorem tsum_biUnion_le_tsum (f : α → ℕ∞) (s : Set ι) (t : ι → Set α) :
    ∑' x : ⋃ i ∈ s , t i, f x ≤ ∑' i : s, ∑' x : t i, f x :=
  calc ∑' x : ⋃ i ∈ s, t i, f x = ∑' x : ⋃ i : s, t i, f x := by rw [tsum_congr_subtype]; simp
  _ ≤ ∑' i : s, ∑' x : t i, f x := ENat.tsum_iUnion_le_tsum _ _

protected theorem tsum_biUnion_le (f : α → ℕ∞) (s : Finset ι) (t : ι → Set α) :
    ∑' x : ⋃ i ∈ s, t i, f x ≤ ∑ i ∈ s, ∑' x : t i, f x :=
  (ENat.tsum_biUnion_le_tsum f s.toSet t).trans_eq (Finset.tsum_subtype s fun i ↦ ∑' x : t i, f x)

protected theorem tsum_iUnion_le [Fintype ι] (f : α → ℕ∞) (t : ι → Set α) :
    ∑' x : ⋃ i, t i, f x ≤ ∑ i, ∑' x : t i, f x := by
  rw [← tsum_fintype]
  exact ENat.tsum_iUnion_le_tsum f t

theorem tsum_iUnion_eq_tsum (f : α → ℕ∞) (t : ι → Set α) (ht : Pairwise (Disjoint on t)) :
    ∑' x : ⋃ i, t i, f x = ∑' i, ∑' x : t i, f x :=
  calc ∑' x : ⋃ i, t i, f x = ∑' x : Σ i, t i, f x.2 :=
    (ENat.tsum_comp_eq_tsum_of_bijective (sigmaToiUnion_bijective t (fun _ _ hij ↦ ht hij)) _).symm
    _ = _ := ENat.tsum_sigma' _

section Card

@[simp] protected theorem tsum_const (c : ℕ∞) : ∑' _ : ι, c = c * ENat.card ι := by
  obtain hι | hι := finite_or_infinite ι
  · have := Fintype.ofFinite ι
    simp [tsum_eq_sum (s := Finset.univ) (by simp), mul_comm]
  obtain rfl | hne := eq_or_ne c 0
  · simp
  rw [ENat.tsum_eq_top_of_support_infinite, card_eq_top_of_infinite, mul_top hne]
  rwa [support_const hne, infinite_univ_iff]

/-- A version of `ENat.tsum_one` where the `1` is explicitly a function from the type rather than
  from the subtype. Useful for rewriting. -/
protected theorem tsum_one' (s : Set α) : ∑' (i : s), (1 : α → ℕ∞) i = s.encard := by
  simp [← encard_univ]

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

protected theorem tsum_encard_eq_encard_iUnion {ι} {s : ι → Set α} (hI : Pairwise (Disjoint on s)) :
    ∑' i, (s i).encard = (⋃ i, s i).encard := by
  simp_rw [← ENat.tsum_one', ENat.tsum_iUnion_eq_tsum _ _ hI]

theorem encard_iUnion_le_tsum_encard {ι} {s : ι → Set α} :
    (⋃ i, s i).encard ≤ ∑' i, (s i).encard := by
  rw [← ENat.tsum_one]
  exact (ENat.tsum_iUnion_le_tsum 1 s).trans_eq <| by simp [encard]

theorem tsum_encard_eq_encard_biUnion {ι} {s : ι → Set α} {t : Set ι}
    (hI : t.PairwiseDisjoint s) : ∑' i : t, (s i).encard = (⋃ i ∈ t, s i).encard := by
  rw [biUnion_eq_iUnion, ← ENat.tsum_encard_eq_encard_iUnion]
  simp_rw [Pairwise, Disjoint]
  aesop

theorem encard_biUnion_le_tsum_encard {ι} {s : ι → Set α} {I : Set ι} :
    (⋃ i ∈ I, s i).encard ≤ ∑' i : I, (s i).encard := by
  rw [biUnion_eq_iUnion]
  apply encard_iUnion_le_tsum_encard

protected theorem tsum_encard_eq_encard_sUnion {c : Set (Set α)} (hc : c.PairwiseDisjoint id) :
    ∑' (t : c), (t : Set α).encard = (⋃₀ c).encard := by
  rw [sUnion_eq_iUnion, ← ENat.tsum_encard_eq_encard_iUnion]
  rintro ⟨i,hi⟩ ⟨j,hj⟩ hij
  exact hc hi hj (by simpa using hij)

theorem encard_sUnion_le_tsum_encard {c : Set (Set α)} :
    (⋃₀ c).encard ≤ ∑' s : c, s.1.encard := by
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
