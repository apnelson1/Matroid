module

public import Matroid.GraphTheory.GraphTopology.Map
public import Matroid.GraphTheory.GraphTopology.Restriction

/-! # Transport and whole-edge restriction

The input set is intersected with the original carrier before taking its image:
the map need not be injective outside the carrier.
-/

@[expose] public section

open Set Function Topology

namespace GraphLike

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (G : GraphLike X) (f : X → Y)
  (hf : IsEmbeddingOn f G.carrier)

/-- Transport commutes with maximal-contained restriction. -/
theorem map_restrict (A : Set X) : (G.restrict A).map f (hf.mono (G.restrict_subset_self A)) =
    (G.map f hf).restrict (f '' (A ∩ G)) := by
  let H := (G.restrict A).map f (hf.mono (G.restrict_subset_self A))
  let K := (G.map f hf).restrict (f '' (A ∩ G))
  change H = K
  have hV : V(H) = V(K) := by
    change f '' (A ∩ V(G)) = f '' (A ∩ G) ∩ f '' V(G)
    rw [← hf.injOn.image_inter inter_subset_right G.subset,
      inter_assoc, inter_eq_right.mpr G.subset]
  have hE : E(H) = E(K) := by
    simp only [H, K, map_edgeSet, restrict_edgeSet]
    ext d
    constructor
    · rintro ⟨e, ⟨he, heA⟩, rfl⟩
      exact ⟨⟨e, he, rfl⟩, image_mono (subset_inter heA (G.edge_subset he))⟩
    · rintro ⟨⟨e, he, rfl⟩, heA⟩
      refine ⟨e, ⟨he, ?_⟩, rfl⟩
      exact ((hf.injOn.image_subset_image_iff (G.edge_subset he) inter_subset_right).mp heA).trans
        inter_subset_left
  exact GraphLike.ext (by
    rw [H.carrier_eq_vertexSet_union_sUnion_edges, K.carrier_eq_vertexSet_union_sUnion_edges,
      hV, hE]) hV

end GraphLike
