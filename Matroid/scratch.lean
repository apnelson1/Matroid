import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Data.ENat.Basic
import Mathlib.Data.Nat.PartENat
import Mathlib.Topology.Order.Basic
import Matroid.ForMathlib.card
import Mathlib.Topology.Instances.ENNReal


open Set 

open scoped BigOperators

namespace ENat

instance : TopologicalSpace ℕ∞ :=
  Preorder.topology ℕ∞

instance : OrderTopology ℕ∞ := 
  ⟨rfl⟩  

variable {f : α → ℕ∞}

protected theorem hasSum : HasSum f (⨆ s : Finset α, ∑ a in s, f a) :=
  tendsto_atTop_iSup fun _ _ => Finset.sum_le_sum_of_subset

-- theorem tsum_insert [TopologicalSpace β] [AddCommMonoid β] (f : α → β) (s : Set α) (hx : x ∉ s) :
--     ∑' (i : (insert x s : Set α) ), f i = f x + ∑' (i : s), f i := by
  



-- theorem tsum_ones (s : Set α) : ∑' (x : s), (1 : ℕ∞) = s.encard := by
--   obtain (hs | hs) := s.finite_or_infinite
--   · apply @Finite.induction_on α _ _ hs
--     · simp
--     intro a s has hs
--     rw [tsum_insert]

-- theorem tsum_eq_top_of_infinite (f : α → ℕ∞) (hf : Set.Infinite f.support) : 
--     ∑' (x : α), f x = ⊤ := by 
--   sorry