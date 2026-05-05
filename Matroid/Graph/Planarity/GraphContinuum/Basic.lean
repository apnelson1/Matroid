import Matroid.Graph.Planarity.Topology.ConnPartition
import Matroid.Graph.Planarity.Topology.Circuit
import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
import Mathlib.Geometry.Manifold.Metrizable
import Mathlib.Topology.Connected.LocallyConnected

variable {G : Type*} {e f C S T : Set G} {v w : G}

open Set Function TopologicalSpace Topology Metric Nat Set.Notation Partition
open scoped unitInterval

/-!
# Basic properties of graph continua
-/

class GraphContinuum (G : Type*) extends EMetricSpace G, CompactSpace G where
  verts : Set G
  totallyDisconnected : IsTotallyDisconnected verts
  graphLike : ∀ T ∈ PathComponentPartition vertsᶜ, T ≃ₜ Ioo (0 : ℝ) 1

namespace GraphContinuum

variable [GraphContinuum G]

scoped notation "V(" G ")" => GraphContinuum.verts (G := G)

def edges (G) [GraphContinuum G] : Partition (Set G) := PathComponentPartition V(G)ᶜ

scoped notation "E(" G ")" => GraphContinuum.edges (G := G)

def homeo_ball (he : e ∈ E(G)) : e ≃ₜ Ioo (0 : ℝ) 1 := graphLike e he

lemma subset_compl_verts_of_mem_edges (he : e ∈ E(G)) : e ⊆ V(G)ᶜ :=
  (subset_of_mem he).trans (by rw [edges, pathComponentPartition_supp])

lemma disjoint_verts_of_mem_edges (he : e ∈ E(G)) : Disjoint e V(G) := by
  rw [disjoint_iff_inter_eq_empty, ← subset_empty_iff]
  refine subset_trans (inter_subset_inter (subset_compl_verts_of_mem_edges he) Subset.rfl) ?_
  simp

lemma isOpen_edge [LocPathConnectedSpace G] (he : e ∈ E(G)) (hV : IsClosed V(G)) : IsOpen e :=
  hV.isOpen_compl.pathComponentPartition_isOpen he

lemma not_isClosed_edge (he : e ∈ E(G)) : ¬ IsClosed e := by
  have hom := homeo_ball he
  rintro hcl
  have := hcl.isCompact
  rw [isCompact_iff_isCompact_univ, ← hom.isCompact_image, image_univ, EquivLike.range_eq_univ,
    ← isCompact_iff_isCompact_univ, isCompact_Ioo_iff] at this
  grind

lemma isPathConnected_edge (he : e ∈ E(G)) : IsPathConnected e := by
  have hom := homeo_ball he
  rw [isPathConnected_iff_pathConnectedSpace, pathConnectedSpace_iff_univ,
    ← hom.isPathConnected_image]
  simp only [image_univ, EquivLike.range_eq_univ]
  have := pathConnectedSpace_Ioo (E := ℝ) (a := 0) (b := 1) (hab := by simp)
  exact isPathConnected_univ

def Inc (e : Set G) (v : G) : Prop := e ∈ E(G) ∧ v ∈ V(G) ∩ closure e

lemma Inc.edge_mem (h : Inc e v) : e ∈ E(G) := h.1
lemma Inc.vertex_mem (h : Inc e v) : v ∈ V(G) := h.2.1

-- lemma exists_inc_of_mem_edges [LocPathConnectedSpace G] (he : e ∈ E(G)) : ∃ v, Inc e v := by
--   -- simp only [Inc, he, mem_inter_iff, true_and, ← not_disjoint_iff]
--   -- by_contra! hdj
--   -- have hconn : IsConnected (closure e) := (isPathConnected_edge he).isConnected.closure
--   -- rw [IsOpen.isConnected_iff_isPathConnected] at hconn
--   sorry

-- noncomputable instance : GraphContinuum Circle where
--   verts := {-1}
--   totallyDisconnected := isTotallyDisconnected_singleton
--   graphLike T hT := by
--     rw [Real.ball_zero_eq_Ioo]
--     replace hT : T = {-1}ᶜ := by
--       sorry
    -- have h := AddCircle.homeomorphCircle (T := 1) (by simp)
    -- |>.symm.trans (AddCircle.homeoIccQuot 1 0)

--     sorry

--     -- apply Equiv.subtypeEquiv

lemma exists_vert_of_circuit (hC : IsCircuit C) : ∃ v ∈ C, v ∈ V(G) := by
  rw [← not_disjoint_iff]
  by_contra! hdj
  obtain ⟨U, hU, hCU⟩ := (hC.isPathConnected).exists_part_pathComponentPartition
    hdj.subset_compl_right
  exact not_isCircuit_real _ <| hC.restrictSubtype hCU |>.image (graphLike U hU).isEmbedding
  |>.image .subtypeVal

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

-- variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
