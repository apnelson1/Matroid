import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Monoid.WithTop
import Mathlib.Data.ENat.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Topology.Algebra.Order.MonotoneConvergence
import Mathlib.Topology.Instances.ENNReal

section SMul

variable {α : Type*} [DecidableEq α]

section Distrib

example [AddCommMonoid α] : DistribSMul ℕ α where
  smul_zero := nsmul_zero
  smul_add x y a := nsmul_add y a x

instance [CanonicallyOrderedAddCommMonoid α] : DistribSMul ℕ∞ (WithTop α) where
  smul n a := n.rec (if a = 0 then 0 else ⊤) (fun i ↦ i • a)
  smul_zero := by
    rintro (rfl | n)
    · change ite _ _ _ = _
      rw [if_pos rfl]
    exact nsmul_zero n
  smul_add := by
    rintro (rfl | n) a b
    · change ite _ _ _ = (ite _ _ _) + (ite _ _ _)
      obtain (rfl | ha) := (zero_le a).eq_or_lt
      · rw [zero_add, if_pos rfl, zero_add]
      rw [if_neg, if_neg ha.ne.symm, WithTop.top_add]
      rw [← Ne.def, ← pos_iff_ne_zero]
      exact ha.trans_le le_self_add
    exact nsmul_add a b n

end Distrib

namespace WithTop

-- variable [Preorder α] [TopologicalSpace α] [OrderTopology α]

-- instance : TopologicalSpace (WithTop α) := Preorder.topology (WithTop α)

-- instance : OrderTopology (WithTop α) := ⟨rfl⟩

set_option trace.Meta.synthInstance true

noncomputable example : CompleteIsLinearOrder ENNReal := by
  exact ENNReal.instCompleteIsLinearOrderENNReal
  -- show_term {infer_instance}

-- #check StrictMono.embedding_of_ordConnected

theorem embedding_coe : Embedding ((↑) : α → WithTop α) := by
  rw [embedding_iff, and_iff_left WithTop.coe_injective, inducing_iff_nhds]
  intro a
  ext s
  simp only [Filter.mem_comap, nhds]
  simp


  -- convert (WithTop.coe_injective (α := α)).embedding_induced
