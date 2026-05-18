import Mathlib.Geometry.Manifold.Instances.Sphere
import Mathlib.Topology.CWComplex.Classical.Graph
import Matroid.Graph.Planarity.Realization.CWComplex
import Matroid.Graph.Planarity.Topology.Circuit
import Matroid.Graphic
import Matroid.ForMathlib.Analysis.Normed.Module.Connected


open Metric Set Graph Topology.RelCWComplex Topology.CWComplex Function Set.Notation

namespace Graph

variable {α β : Type*} {G : Graph α β}

structure CellularEmbedding (G : Graph α β) (E : Type*) [TopologicalSpace E] : Type _ where
  toFun : G.Realization → E
  embedding : Topology.IsEmbedding toFun
  cellular : ∀ x ∉ range toFun, Nonempty ((connectedComponentIn (range toFun)ᶜ x) ≃ₜ ball (0 : ℂ) 1)

namespace CellularEmbedding

section TopologicalSpace

variable {E : Type*} [TopologicalSpace E] {φ : CellularEmbedding G E}

instance : FunLike (CellularEmbedding G E) G.Realization E where
  coe := CellularEmbedding.toFun
  coe_injective' φ₁ φ₂ h := by cases φ₁; cases φ₂; simpa

@[reducible]
def Faces (φ : CellularEmbedding G E) := ConnectedComponents ↑((range φ.toFun)ᶜ)

def FaceMk (f : Faces φ) : Set E := Subtype.val '' ConnectedComponents.mk ⁻¹' {f}

lemma faceMk_nonempty (f : Faces φ) : (FaceMk f).Nonempty := by
  simp only [FaceMk, ConnectedComponents.mk, image_nonempty]
  exact Quotient.mk''_surjective.nonempty_preimage.mpr <| singleton_nonempty f

lemma faceMk_disjoint_range (f : Faces φ) : Disjoint (FaceMk f) (range φ.toFun) := by
  simp only [FaceMk, ConnectedComponents.mk]
  rw [disjoint_iff_forall_notMem]
  rintro _ ⟨x, _, rfl⟩
  exact x.prop

lemma faceMk_eq_connectedComponentIn (f : Faces φ) (x : E)
    (hx : x ∈ FaceMk f) : FaceMk f = connectedComponentIn (range φ.toFun)ᶜ x := by
  have hxran : x ∉ range φ.toFun := (φ.faceMk_disjoint_range f).subset_compl_right hx
  simp only [FaceMk, mem_image, mem_preimage, mem_singleton_iff, Subtype.exists, mem_compl_iff,
    mem_range, not_exists, exists_and_right, exists_eq_right] at hx ⊢
  obtain ⟨_, rfl⟩ := hx
  ext y
  rw [connectedComponentIn_eq_image hxran]
  simp [← connectedComponent_eq_iff_mem, ConnectedComponents.coe_eq_coe]

lemma homeomorphism_faceMk (f : Faces φ) : Nonempty (FaceMk f ≃ₜ ball (0 : ℂ) 1) := by
  obtain ⟨x, hx⟩ := φ.faceMk_nonempty f
  obtain h := φ.cellular x <| (φ.faceMk_disjoint_range f).subset_compl_right hx
  rwa [← φ.faceMk_eq_connectedComponentIn f x hx] at h

def drawing (φ : CellularEmbedding G E) : Set E := range φ.toFun

lemma vertexMK_mem_drawing (v : V(G)) : φ (vertexMk v) ∈ drawing φ := by
  use vertexMk v
  rfl

lemma edge_subset_drawing (e : E(G)) : range (φ ∘ edgePath e) ⊆ drawing φ := by
  rintro x ⟨t, ht, rfl⟩
  use (edgePath e) t
  rfl

-- instance : Topology.CWComplex (univ : Set E) where
--   cell n := match n with
--     | 0 => ULift.{u_2, u_3} V(G)
--     | 1 => ULift E(G)
--     | _ + 2 => ULift.{max u v, 0} Empty


end TopologicalSpace

section surface

variable {E : Type*} [TopologicalSpace E] [T2Space E] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) E]
  [BoundarylessManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 2))) E]

-- def dualGraph (φ : CellularEmbedding G E) : Graph φ.Faces β where
--   vertexSet := univ
--   edgeSet := E(G)
--   IsLink e x y := ∃ he : e ∈ E(G),
--     range (φ ∘ edgePath ⟨e, he⟩) ⊆ frontier (FaceMk x) ∩ frontier (FaceMk y)
--   isLink_symm e he x y h := by
--     simp_rw [inter_comm]
--     exact h
--   eq_or_eq_of_isLink_of_isLink e u v x y huv hxy := by
--     obtain ⟨_, huv⟩ := huv
--     obtain ⟨he, hxy⟩ := hxy
--     sorry
--   edge_mem_iff_exists_isLink e := by
--     refine ⟨fun he ↦ ?_, by grind⟩
--     sorry
