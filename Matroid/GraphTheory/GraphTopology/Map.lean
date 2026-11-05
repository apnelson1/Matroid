module

public import Matroid.GraphTheory.GraphTopology.Basic
public import Mathlib.Topology.Homeomorph.Lemmas

/-! # Embedding transport of graph-like spaces

Only the restriction of the map to the carrier is required to be an embedding.
Edges are transported by set image; connected components are used only in the construction.
-/

@[expose] public section

open Set Function Topology Set.Notation

namespace GraphLike

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

private noncomputable def componentEquiv (h : X ≃ₜ Y) :
    ConnectedComponents X ≃ ConnectedComponents Y where
  toFun := (ConnectedComponents.continuous_coe.comp h.continuous).connectedComponentsLift
  invFun := (ConnectedComponents.continuous_coe.comp h.symm.continuous).connectedComponentsLift
  left_inv e := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe e
    change ConnectedComponents.mk (h.symm (h x)) = ConnectedComponents.mk x
    rw [h.symm_apply_apply]
  right_inv e := by
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe e
    change ConnectedComponents.mk (h (h.symm x)) = ConnectedComponents.mk x
    rw [h.apply_symm_apply]

variable (G : GraphLike X) (f : X → Y)
  (hf : IsEmbedding (fun x : G.carrier ↦ f x.1))

include hf

/-- The homeomorphism from the original carrier onto its image. -/
noncomputable def mapCarrierHomeomorph : G.carrier ≃ₜ ↥(f '' G.carrier) :=
  hf.toHomeomorph.trans (.setCongr (by ext y; simp))

@[simp] theorem mapCarrierHomeomorph_apply (x : G.carrier) :
    (G.mapCarrierHomeomorph f hf x).1 = f x.1 := rfl

/-- Injectivity is needed only at points of the carrier. -/
theorem map_injOn : InjOn f G.carrier := by
  intro x hx y hy h
  exact congrArg Subtype.val (hf.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) h)

/-- Continuity is needed only on the carrier. -/
theorem map_continuousOn : ContinuousOn f G.carrier :=
  continuousOn_iff_continuous_domRestrict.mpr hf.continuous

private theorem preimage_image {S : Set X} (hS : S ⊆ G.carrier) :
    (G.mapCarrierHomeomorph f hf) ⁻¹' (Subtype.val ⁻¹' (f '' S)) =
      (Subtype.val ⁻¹' S : Set G.carrier) := by
  ext x
  change f x.1 ∈ f '' S ↔ x.1 ∈ S
  exact ⟨fun ⟨y, hy, heq⟩ ↦ (G.map_injOn f hf (hS hy) x.2 heq) ▸ hy,
    fun hx ↦ mem_image_of_mem f hx⟩

private theorem image_relative_closure {S : Set X} (hS : S ⊆ G.carrier) :
    (f '' G.carrier) ∩ closure (f '' S) = f '' (G.carrier ∩ closure S) := by
  have hpre := (G.mapCarrierHomeomorph f hf).preimage_closure (Subtype.val ⁻¹' (f '' S))
  rw [preimage_image G f hf hS] at hpre
  rw [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image,
    IsEmbedding.subtypeVal.closure_eq_preimage_closure_image] at hpre
  simp only [Subtype.image_preimage_coe, inter_eq_right.mpr hS,
    inter_eq_right.mpr (image_mono hS)] at hpre
  ext y
  constructor
  · rintro ⟨⟨x, hx, rfl⟩, hy⟩
    exact ⟨x, ⟨hx, (Set.ext_iff.mp hpre ⟨x, hx⟩).mp hy⟩, rfl⟩
  · rintro ⟨x, ⟨hx, hcl⟩, rfl⟩
    exact ⟨mem_image_of_mem f hx, (Set.ext_iff.mp hpre ⟨x, hx⟩).mpr hcl⟩

private noncomputable def complementHomeomorph :
    ↥(G.carrier \ G.vertexSet) ≃ₜ ↥((f '' G.carrier) \ (f '' G.vertexSet)) := by
  let F : ↥(G.carrier \ G.vertexSet) → ↥((f '' G.carrier) \ (f '' G.vertexSet)) :=
    fun x ↦ ⟨f x.1, mem_image_of_mem f x.2.1, by
      rintro ⟨v, hv, heq⟩
      exact x.2.2 ((G.map_injOn f hf (G.subset hv) x.2.1 heq) ▸ hv)⟩
  have hF : IsEmbedding F :=
    (hf.comp (IsEmbedding.inclusion (show G.carrier \ G.vertexSet ⊆ G.carrier from
      sdiff_subset))).codRestrict _ (fun x ↦ (F x).property)
  exact hF.toHomeomorphOfSurjective (by
    rintro ⟨y, ⟨x, hx, rfl⟩, hy⟩
    exact ⟨⟨x, hx, fun hv ↦ hy (mem_image_of_mem f hv)⟩, rfl⟩)

private noncomputable def imageComponentEquiv :
    ConnectedComponents ↥(G.carrier \ V(G)) ≃
      ConnectedComponents ↥((f '' G.carrier) \ (f '' G.vertexSet)) :=
  componentEquiv (G.complementHomeomorph f hf)

private theorem imageComponent_interior (e : ConnectedComponents ↥(G.carrier \ V(G))) :
    Subtype.val '' (G.imageComponentEquiv f hf e).toSet =
      f '' (Subtype.val '' e.toSet) := by
  ext y
  constructor
  · rintro ⟨z, hz, rfl⟩
    obtain ⟨x, rfl⟩ := (G.complementHomeomorph f hf).surjective z
    have hx : ConnectedComponents.mk x = e := (G.imageComponentEquiv f hf).injective hz
    exact ⟨x.1, ⟨x, hx, rfl⟩, rfl⟩
  · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨G.complementHomeomorph f hf z, congrArg (G.imageComponentEquiv f hf) hz, rfl⟩

private theorem imageComponent_range (e : ConnectedComponents ↥(G.carrier \ V(G))) :
    (f '' G.carrier) ∩ closure
      (Subtype.val '' (G.imageComponentEquiv f hf e).toSet) =
        f '' (G.carrier ∩ closure (Subtype.val '' e.toSet)) := by
  rw [imageComponent_interior]
  exact G.image_relative_closure f hf (by rintro _ ⟨x, _, rfl⟩; exact x.2.1)

private theorem imageComponent_boundary (e : ConnectedComponents ↥(G.carrier \ V(G))) :
    ((f '' G.carrier) ∩ closure
      (Subtype.val '' (G.imageComponentEquiv f hf e).toSet)) \
      (Subtype.val '' (G.imageComponentEquiv f hf e).toSet) =
        f '' ((G.carrier ∩ closure (Subtype.val '' e.toSet)) \ (Subtype.val '' e.toSet)) := by
  rw [imageComponent_range, imageComponent_interior]
  exact ((G.map_injOn f hf).mono inter_subset_left).image_sdiff_subset
    (by rintro _ ⟨x, hx, rfl⟩; exact ⟨x.2.1, subset_closure ⟨x, hx, rfl⟩⟩) |>.symm

/-- Transport a graph-like space by an embedding of its carrier. -/
noncomputable def map : GraphLike Y where
  carrier := f '' G.carrier
  vertexSet := f '' G.vertexSet
  t2Space := (G.mapCarrierHomeomorph f hf).symm.isEmbedding.t2Space
  subset := image_mono G.subset
  isClosed := by
    rw [← (G.mapCarrierHomeomorph f hf).isClosed_preimage,
      preimage_image G f hf G.subset]
    exact G.isClosed
  isTotallySeparated := by
    let h := G.mapCarrierHomeomorph f hf
    intro x hx y hy hxy
    have hx' : h.symm x ∈ (Subtype.val ⁻¹' G.vertexSet : Set G.carrier) := by
      rw [← preimage_image G f hf G.subset]
      simpa [h] using hx
    have hy' : h.symm y ∈ (Subtype.val ⁻¹' G.vertexSet : Set G.carrier) := by
      rw [← preimage_image G f hf G.subset]
      simpa [h] using hy
    obtain ⟨U, V, hU, hV, hxU, hyV, hcover, hdisj⟩ :=
      G.isTotallySeparated hx' hy' (h.symm.injective.ne hxy)
    refine ⟨h.symm ⁻¹' U, h.symm ⁻¹' V, hU.preimage h.symm.continuous,
      hV.preimage h.symm.continuous, hxU, hyV, ?_, hdisj.preimage _⟩
    intro z hz
    apply hcover
    rw [← preimage_image G f hf G.subset]
    simpa [h] using hz
  interior_isOpen' := by
    intro C
    obtain ⟨e, rfl⟩ := (G.imageComponentEquiv f hf).surjective C
    rw [imageComponent_interior, ← (G.mapCarrierHomeomorph f hf).isOpen_preimage,
      preimage_image G f hf (by rintro _ ⟨x, _, rfl⟩; exact x.2.1)]
    exact G.interior_isOpen' e
  boundary_isPair' := by
    intro C
    obtain ⟨e, rfl⟩ := (G.imageComponentEquiv f hf).surjective C
    obtain ⟨x, y, hb, hl⟩ := G.boundary_isPair' e
    refine ⟨⟨f x.1, mem_image_of_mem f x.2⟩, ⟨f y.1, mem_image_of_mem f y.2⟩, ?_, ?_⟩
    · change _ = {f x.1, f y.1}
      rw [imageComponent_boundary, hb, image_pair]
    · change IsPrimitiveLink _ (f x.1) (f y.1)
      rw [imageComponent_range]
      exact hl.image ((G.map_continuousOn f hf).mono inter_subset_left)
        ((G.map_injOn f hf).mono inter_subset_left)

@[simp] theorem map_carrier : (G.map f hf).carrier = f '' G.carrier := rfl
@[simp] theorem map_vertexSet : (G.map f hf).vertexSet = f '' G.vertexSet := rfl

/-- The image edge set consists exactly of the images of original edges. -/
@[simp] theorem map_edgeSet : E(G.map f hf) = (Set.image f) '' E(G) := by
  ext d
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨e, rfl⟩ := (G.imageComponentEquiv f hf).surjective c
    exact ⟨G.carrier ∩ closure (Subtype.val '' e.toSet), G.componentClosure_mem_edgeSet e,
      (G.imageComponent_range f hf e).symm⟩
  · rintro ⟨e, ⟨c, rfl⟩, rfl⟩
    exact ⟨G.imageComponentEquiv f hf c, G.imageComponent_range f hf c⟩

/-- The exact correspondence of geometric edges under carrier embeddings. -/
noncomputable def mapEdgeEquiv : ↥E(G) ≃ ↥E(G.map f hf) :=
  Equiv.ofBijective (fun e ↦ ⟨f '' e.1, by rw [map_edgeSet]; exact ⟨e.1, e.2, rfl⟩⟩) (by
    constructor
    · intro e d h
      apply Subtype.ext
      have hi : f '' e.1 = f '' d.1 := congrArg Subtype.val h
      ext x
      constructor
      · intro hx
        obtain ⟨y, hy, hyx⟩ := hi ▸ mem_image_of_mem f hx
        exact (G.map_injOn f hf (G.edge_subset d.2 hy) (G.edge_subset e.2 hx) hyx) ▸ hy
      · intro hx
        obtain ⟨y, hy, hyx⟩ := hi.symm ▸ mem_image_of_mem f hx
        exact (G.map_injOn f hf (G.edge_subset e.2 hy) (G.edge_subset d.2 hx) hyx) ▸ hy
    · rintro ⟨d, hd⟩
      rw [map_edgeSet] at hd
      obtain ⟨e, he, rfl⟩ := hd
      exact ⟨⟨e, he⟩, rfl⟩)

@[simp] theorem mapEdge_coe (e : E(G)) :
    (G.mapEdgeEquiv f hf e).1 = f '' e.1 := rfl

@[simp] theorem mapEdge_interior {e : Set X} (he : e ∈ E(G)) :
    (G.map f hf).edgeInterior (f '' e) = f '' G.edgeInterior e := by
  obtain ⟨c, rfl⟩ := he
  rw [G.edgeInterior_componentClosure, ← G.imageComponent_range f hf c]
  exact ((G.map f hf).edgeInterior_componentClosure _).trans
    (G.imageComponent_interior f hf c)

@[simp] theorem mapEdge_boundary {e : Set X} (he : e ∈ E(G)) :
    (G.map f hf).edgeBoundary (f '' e) = f '' G.edgeBoundary e := by
  obtain ⟨c, rfl⟩ := he
  rw [G.edgeBoundary_componentClosure, ← G.imageComponent_range f hf c]
  exact ((G.map f hf).edgeBoundary_componentClosure _).trans
    (G.imageComponent_boundary f hf c)

/-- Finiteness of vertices and edges is preserved and reflected. -/
theorem map_finite_iff : (G.map f hf).Finite ↔ G.Finite := by
  constructor
  · intro h
    let := h
    have : _root_.Finite E(G) :=
      _root_.Finite.of_equiv ↥E(G.map f hf) (G.mapEdgeEquiv f hf).symm
    exact ⟨h.vertexSet_finite.of_finite_image ((G.map_injOn f hf).mono G.subset),
      Set.toFinite _⟩
  · intro h
    refine ⟨h.vertexSet_finite.image f, ?_⟩
    rw [map_edgeSet]
    exact h.edgeSet_finite.image _

omit hf in
@[simp] theorem map_id (h : IsEmbedding (fun x : G.carrier ↦ x.1)) :
    G.map id h = G := by
  apply GraphLike.ext <;> simp

/-- The carrier embedding needed for successive transports. -/
theorem map_comp_isEmbedding (g : Y → Z)
    (hg : IsEmbedding (fun y : (G.map f hf).carrier ↦ g y.1)) :
    IsEmbedding (fun x : G.carrier ↦ (g ∘ f) x.1) :=
  hg.comp (G.mapCarrierHomeomorph f hf).isEmbedding

theorem map_comp (g : Y → Z)
    (hg : IsEmbedding (fun y : (G.map f hf).carrier ↦ g y.1)) :
    (G.map f hf).map g hg = G.map (g ∘ f) (G.map_comp_isEmbedding f hf g hg) := by
  apply GraphLike.ext <;> simp [image_image]

end GraphLike
