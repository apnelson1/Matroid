module

public import Matroid.GraphTheory.GraphTopology.Basic
public import Matroid.ForMathlib.Topology.IsEmbeddingOn

/-! # Embedding transport of graph-like spaces

Only the restriction of the map to the carrier is required to be an embedding.
Edges are transported by set image; connected components are used only in the construction.
-/

@[expose] public section

open Set Function Topology Set.Notation

namespace GraphLike

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] {S : Set X}
  {G : GraphLike X} {f : X → Y} (hf : IsEmbeddingOn f G.carrier) {e : Set X} (he : e ⊆ G.carrier)

/-- Transport a graph-like space by an embedding of its carrier. -/
noncomputable def map (G : GraphLike X) (f : X → Y) (hf : IsEmbeddingOn f G.carrier) :
    GraphLike Y where
  carrier := f '' G.carrier
  vertexSet := f '' G.vertexSet
  t2Space := hf.homeomorphImage.symm.isEmbedding.t2Space
  subset := image_mono G.subset
  isClosed := by
    rw [← hf.homeomorphImage.isClosed_preimage, hf.homeomorphImage_preimage_image G.subset]
    exact G.isClosed
  isTotallySeparated := by
    let h := hf.homeomorphImage
    rw [← hf.homeomorphImage_image G.subset]
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ hxy
    obtain ⟨U, V, hU, hV, hxU, hyV, hcover, hdisj⟩ :=
      G.isTotallySeparated hx hy <| h.injective.ne_iff.mp hxy
    refine ⟨h '' U, h '' V, h.isOpenMap _ hU, h.isOpenMap _ hV,
      mem_image_of_mem h hxU, mem_image_of_mem h hyV, ?_,
      disjoint_image_of_injective h.injective hdisj⟩
    simpa only [image_union] using image_mono hcover
  interior_isOpen' := by
    rintro _ ⟨⟨p, hp, rfl⟩, hpV⟩
    simpa only [← hf.injOn.image_sdiff_subset G.subset,
      ← hf.image_connectedComponentIn sdiff_subset hp, ← hf.homeomorphImage.isOpen_preimage,
      hf.homeomorphImage_preimage_image <| (connectedComponentIn_subset ..).trans sdiff_subset]
      using G.interior_isOpen' p (⟨hp, (hpV <| mem_image_of_mem f ·)⟩)
  boundary_isPair' := by
    rintro _ ⟨⟨p, hp, rfl⟩, hpV⟩
    dsimp only
    rw [← hf.injOn.image_sdiff_subset G.subset,
      ← hf.image_relative_closure_connectedComponentIn sdiff_subset hp,
      ← hf.image_connectedComponentIn sdiff_subset hp]
    obtain ⟨x, y, hb, hl⟩ := G.boundary_isPair' p (⟨hp, (hpV <| mem_image_of_mem f ·)⟩)
    refine ⟨⟨f x.val, mem_image_of_mem f x.prop⟩, ⟨f y.val, mem_image_of_mem f y.prop⟩, ?_, ?_⟩
    · rw [← (hf.injOn.mono inter_subset_left).image_sdiff_subset <|
      subset_inter ((connectedComponentIn_subset ..).trans sdiff_subset) subset_closure,
      hb, image_pair]
    exact hl.image (hf.continuousOn.mono inter_subset_left) <| hf.injOn.mono inter_subset_left

@[simp] theorem map_carrier : (G.map f hf).carrier = f '' G.carrier := rfl

@[simp] theorem map_vertexSet : (G.map f hf).vertexSet = f '' G.vertexSet := rfl

/-- Transport preserves closure relative to the carrier. -/
theorem map_image_relative_closure (hS : S ⊆ G.carrier) :
    (G.map f hf).carrier ∩ closure (f '' S) = f '' (G.carrier ∩ closure S) :=
  (hf.image_relative_closure hS).symm

/-- The image edge set consists exactly of the images of original edges. -/
@[simp] theorem map_edgeSet : E(G.map f hf) = image f '' E(G) := by
  have hcompl : f '' (G.carrier \ V(G)) = (G.map f hf).carrier \ V(G.map f hf) :=
    hf.injOn.image_sdiff_subset G.subset
  have hclosure {p : X} (hp : p ∈ G.carrier) : (G.map f hf).carrier ∩
    (closure <| connectedComponentIn ((G.map f hf).carrier \ V(G.map f hf)) <| f p) =
      f '' (G.carrier ∩ closure (connectedComponentIn (G.carrier \ V(G)) p)) := by
    rw [← hcompl]
    exact (hf.image_relative_closure_connectedComponentIn sdiff_subset hp).symm
  ext d
  constructor
  · rintro ⟨_, ⟨⟨p, hp, rfl⟩, hpV⟩, rfl⟩
    exact
      ⟨_, G.componentClosure_mem_edgeSet (⟨hp, (hpV <| mem_image_of_mem f ·)⟩), (hclosure hp).symm⟩
  rintro ⟨e, ⟨p, hp, rfl⟩, rfl⟩
  exact ⟨f p, hcompl.subset <| mem_image_of_mem f hp, hclosure hp.left⟩

include he

@[simp] theorem mapEdge_interior : (G.map f hf).edgeInterior (f '' e) = f '' G.edgeInterior e := by
  rw [edgeInterior, edgeInterior, map_vertexSet, (hf.injOn.mono he).image_sdiff,
    hf.injOn.image_inter he G.subset, sdiff_self_inter]

@[simp] theorem mapEdge_boundary : (G.map f hf).edgeBoundary (f '' e) = f '' G.edgeBoundary e :=
  (hf.injOn.image_inter he G.subset).symm

omit he

omit hf in
@[simp] theorem map_id : G.map id (.id _) = G := by
  refine ext ?_ ?_ <;> simp

variable {g : Y → Z} in
theorem map_comp (hg : IsEmbeddingOn g (G.map f hf).carrier) :
    (G.map f hf).map g hg = G.map (g ∘ f) (hg.comp_image hf) := by
  refine ext ?_ ?_ <;> simp [image_image]

/-- The homeomorphism between the carriers of a graph-like space and its transport. -/
noncomputable def mapCarrierHomeomorph (G : GraphLike X) (f : X → Y)
    (hf : IsEmbeddingOn f G.carrier) : G.carrier ≃ₜ (G.map f hf).carrier := hf.homeomorphImage

@[simp] theorem mapCarrierHomeomorph_apply (x : G.carrier) :
    (G.mapCarrierHomeomorph f hf x).val = f x.val := rfl

theorem mapCarrierHomeomorph_symm_apply (y : (G.map f hf).carrier) :
    f ((G.mapCarrierHomeomorph f hf).symm y).val = y.val :=
  congrArg Subtype.val <| (G.mapCarrierHomeomorph f hf).apply_symm_apply y

variable (hS : S ⊆ G.carrier)
include hS

@[simp] theorem mapCarrierHomeomorph_preimage_image :
    G.mapCarrierHomeomorph f hf ⁻¹' (G.map f hf).carrier ↓∩ f '' S = G.carrier ↓∩ S :=
  hf.homeomorphImage_preimage_image hS

@[simp] theorem mapCarrierHomeomorph_image : G.mapCarrierHomeomorph f hf '' G.carrier ↓∩ S =
      (G.map f hf).carrier ↓∩ f '' S := hf.homeomorphImage_image hS

omit hS

/-- The exact correspondence of geometric edges under carrier embeddings. -/
noncomputable def mapEdgeEquiv : ↥E(G) ≃ ↥E(G.map f hf) :=
  Equiv.ofBijective (fun e ↦ {
    val := f '' e.val
    property := by rw [map_edgeSet]; exact ⟨e.val, e.prop, rfl⟩ }) (by
    constructor
    · exact fun e d h ↦ Subtype.ext <| hf.injOn.image (G.edge_subset e.prop) (G.edge_subset d.prop)
      <| congrArg Subtype.val h
    rintro ⟨d, hd⟩
    rw [map_edgeSet] at hd
    obtain ⟨e, he, rfl⟩ := hd
    exact ⟨⟨e, he⟩, rfl⟩)

@[simp] theorem mapEdge_coe (e : E(G)) : (G.mapEdgeEquiv hf e).val = f '' e.val := rfl

/-- Finiteness of vertices and edges is preserved and reflected. -/
theorem map_finite_iff : (G.map f hf).Finite ↔ G.Finite := by
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨h.vertexSet_finite.image f, ?_⟩⟩
  · have : _root_.Finite E(G) := Finite.of_equiv ↥E(G.map f hf) (G.mapEdgeEquiv hf).symm
    exact ⟨h.vertexSet_finite.of_finite_image <| hf.injOn.mono G.subset, toFinite _⟩
  rw [map_edgeSet]
  exact h.edgeSet_finite.image _

end GraphLike
