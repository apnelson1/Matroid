module

public import Matroid.GraphTheory.GraphTopology.Map
public import Matroid.GraphTheory.GraphTopology.StraightLine

/-! # Affine transport of straight-line and polygonal graph-like spaces -/

@[expose] public section

open Set Function Topology

namespace GraphLike

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [AddCommGroup X] [Module ℝ X]
  [AddCommGroup Y] [Module ℝ Y] {G : GraphLike X}

/-- An affine map embedding the carrier preserves straight-line edges. -/
theorem map_isStraightLine (hG : G.IsStraightLine) (f : X →ᵃ[ℝ] Y)
    (hf : IsEmbeddingOn f G.carrier) : (G.map f hf).IsStraightLine := by
  intro e he x y hb
  rw [G.map_edgeSet hf] at he
  obtain ⟨d, hd, rfl⟩ := he
  obtain ⟨a, -, b, -, hab, -⟩ := G.boundary_isPair hd
  rw [G.mapEdge_boundary hf (G.edge_subset hd), hab, image_pair, pair_eq_pair_iff] at hb
  rw [hG hd hab, image_segment]
  obtain ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ := hb
  · rfl
  exact segment_symm ℝ _ _

/-- Affine carrier embeddings preserve polygonal edges, including loops. -/
theorem map_isPolygonal (hG : G.IsPolygonal) (f : X →ᵃ[ℝ] Y)
    (hf : IsEmbeddingOn f G.carrier) : (G.map f hf).IsPolygonal := by
  intro e he
  rw [G.map_edgeSet hf] at he
  obtain ⟨d, hd, rfl⟩ := he
  exact (hG hd).image f

end GraphLike
