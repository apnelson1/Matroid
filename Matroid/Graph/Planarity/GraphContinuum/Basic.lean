import Matroid.Graph.Planarity.Topology.ConnPartition
import Matroid.Graph.Planarity.Topology.Circuit
import Mathlib.Geometry.Manifold.Metrizable

variable {α β : Type*} {G : Graph α β} {C S T : Set α}

open Set Function TopologicalSpace Topology Relation UniformSpace Sum Path
open scoped unitInterval

/-!
# Basic properties of graph continua
-/

class GraphContinuum (α : Type*) extends EMetricSpace α, CompactSpace α where
  verts : Set α
  totallyDisconnected : IsTotallyDisconnected verts
  graphLike : ∀ T ∈ ComponentPartition verts, T ≃ₜ (Metric.ball 0 1 : Set ℝ)

namespace GraphContinuum

variable [GraphContinuum α] {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

scoped notation "V(" α ")" => GraphContinuum.verts (α := α)

def edges (α) [GraphContinuum α] : Partition (Set α) := ComponentPartition V(α)

scoped notation "E(" α ")" => GraphContinuum.edges (α := α)

def homeo_ball (hT : T ∈ E(α)) : T ≃ₜ (Metric.ball 0 1 : Set ℝ) := graphLike T hT

-- lemma exists_vert_of_circuit (hC : IsCircuit C) : ∃ v ∈ C, v ∈ V(α) := by
--   rw [← not_disjoint_iff]
--   by_contra! hdj
--   obtain ⟨U, hU, hCU⟩ := (hC.pathConnected).exists_part_componentPartition_of_disjoint hdj.symm
--   have := graphLike U hU
--   sorry

-- def dualGraph (f : α → E) (hf : Topology.IsEmbedding f) : Graph (Set E) (Set α) where
--   vertexSet := ComponentPartition (range f)
--   edgeSet := E(α)
--   IsLink e x y := e ∈ E(α) ∧ x ∈ ComponentPartition (range f) ∧
--     y ∈ ComponentPartition (range f) ∧ f '' e ⊆ frontier x ∩ frontier y
--   isLink_symm e he x y h := by
--     obtain ⟨he, hx, hy, h⟩ := h
--     exact ⟨he, hy, hx, inter_comm _ _ ▸ h⟩
--   left_mem_of_isLink e x y h := by
--     obtain ⟨he, hx, hy, h⟩ := h
--     exact hx
--   eq_or_eq_of_isLink_of_isLink e u v x y huv hxy := by
--     obtain ⟨he, hu, hv, huv⟩ := huv
--     obtain ⟨-, hx, hy, hxy⟩ := hxy
