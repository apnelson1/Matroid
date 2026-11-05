module

public import Matroid.GraphTheory.GraphTopology.Map
public import Matroid.GraphTheory.GraphTopology.Restriction

/-! # Transport and whole-edge restriction

Transport by a carrier embedding commutes with selecting vertices and whole edges.
Selections are normalized before transport: the map need not be injective outside the carrier.
-/

@[expose] public section

open Set Function Topology

namespace GraphLike

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
variable (G : GraphLike X) (f : X → Y)
  (hf : IsEmbedding (fun x : G.carrier ↦ f x.1))

/-- Transport of a support is the support of its transported, normalized selections. -/
theorem map_support (A : Set X) (B : Set (Set X)) :
    f '' G.support A B =
      (G.map f hf).support (f '' (A ∩ V(G))) ((Set.image f) '' (B ∩ E(G))) := by
  have hv : f '' (A ∩ V(G)) ⊆ V(G.map f hf) := image_mono inter_subset_right
  have he : (Set.image f) '' (B ∩ E(G)) ⊆ E(G.map f hf) := by
    rw [G.map_edgeSet]
    exact image_mono inter_subset_right
  rw [support, support, inter_eq_left.mpr hv, inter_eq_left.mpr he, image_union]
  congr 1
  ext y
  simp only [mem_image, mem_sUnion]
  constructor
  · rintro ⟨x, ⟨e, he, hx⟩, rfl⟩
    exact ⟨f '' e, ⟨e, he, rfl⟩, x, hx, rfl⟩
  · rintro ⟨_, ⟨e, he, rfl⟩, x, hx, rfl⟩
    exact ⟨x, ⟨e, he, hx⟩, rfl⟩

/-- Transport commutes with restriction as an equality of graph-like spaces. -/
theorem map_restrict (A : Set X) (B : Set (Set X)) :
    (G.restrict A B).map f (hf.comp (IsEmbedding.inclusion (G.support_subset A B))) =
      (G.map f hf).restrict (f '' (A ∩ V(G))) ((Set.image f) '' (B ∩ E(G))) := by
  apply GraphLike.ext (G.map_support f hf A B)
  change f '' (G.support A B ∩ V(G)) =
    (G.map f hf).support (f '' (A ∩ V(G))) ((Set.image f) '' (B ∩ E(G))) ∩
      (f '' V(G))
  rw [← G.map_support f hf A B]
  exact (G.map_injOn f hf).image_inter (G.support_subset A B) G.subset

end GraphLike
