
import Matroid.ForMathlib.card
import Matroid.ForMathlib.PartitionOf
import Mathlib.Algebra.BigOperators.Finprod

/-
  The theorems here are about `finsum`, but really for `encard`, the more natural summation is 
  `tsum`, which would correctly assign the value `⊤` to infinitely supported sums. This would 
  require some topology API for `ENat`. In the maintme, we use finiteness hypotheses. 
-/


open Set

-- theorem finsum_eq_finsum_iff_of_le {ι M : Type _} [inst : OrderedCancelAddCommMonoid M] 
-- {s : Set ι} {f g : ι → M} (h : ∀ (i : ι), f i ≤ g i) :
-- ((Finset.sum s fun i => f i) = Finset.sum s fun i => g i) ↔ ∀ (i : ι), i ∈ s → f i = g i

variable {α : Type _} {s : Set α} {c : Set (Set α)}

theorem ENat.finsum_mem_one_eq (hs : s.Finite) : ∑ᶠ i ∈ s, 1 = s.encard := by 
  apply @Finite.induction_on α _ _ hs
  · simp
  rintro a s has hs IH
  rw [finsum_mem_insert _ has hs, add_comm, IH, encard_insert_of_not_mem has]

theorem ENat.finsum_mem_sUnion_eq (hc : c.PairwiseDisjoint id) (hfin : c.Finite) :
    ∑ᶠ t ∈ c, t.encard = (⋃₀ c).encard := by 
  revert hc
  apply @Finite.induction_on (Set α) _ _ hfin
  · simp_rw [mem_empty_iff_false, finsum_false, finsum_zero]
    rw [sUnion_empty, encard_empty]; exact fun _ ↦ rfl
  rintro a s has hs IH hdj
  rw [finsum_mem_insert _ has hs, IH (hdj.subset (subset_insert _ _)), sUnion_insert, 
    encard_union_eq]
  rw [disjoint_sUnion_right]
  exact fun t hts ↦ hdj (mem_insert _ _) (mem_insert_of_mem _ hts) (by rintro rfl; exact has hts)



  
theorem PSetoid.IsPartition.sum_encard_eq (hc : PSetoid.IsPartition c s) (hs : s.Finite) : 
    ∑ᶠ t ∈ c, t.encard = s.encard := by 
  rw [ENat.finsum_mem_sUnion_eq hc.pairwiseDisjoint (hc.finite_of_finite hs), hc.sUnion_eq]


