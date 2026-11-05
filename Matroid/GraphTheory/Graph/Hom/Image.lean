module

public import Matroid.Graph.Hom.Basic
public import Matroid.Graph.Subgraph.Delete

/-!
# Images and surjective graph homomorphisms

`Hom.vertexImage` and `Hom.edgeImage` are the ranges of the vertex and edge maps.
`Hom.Image` is the subgraph of the host with exactly those vertices and edges, including
the images of isolated vertices. Every homomorphism factors through this subgraph by a map
surjective on both vertex and edge sets. If both maps are injective, this factor is an isomorphism.
`Hom.Surjective` means that the image is the whole target. Embeddings and isomorphisms
inherit the image construction from `Hom`.
-/

@[expose] public section

open Function Set

namespace Graph

variable {V₀ E₀ V₁ E₁ V₂ E₂ : Type*} {G : Graph V₀ E₀} {H : Graph V₁ E₁} {K : Graph V₂ E₂}

namespace Hom

/-- The image of the vertex map. -/
def vertexImage (F : Hom G H) : Set V₁ := range fun x : V(G) ↦ (F.vertMap x).1

/-- The image of the edge map. -/
def edgeImage (F : Hom G H) : Set E₁ := range fun e : E(G) ↦ (F.edgeMap e).1

/-- The image subgraph, including the images of isolated vertices. -/
def Image (F : Hom G H) : Graph V₁ E₁ := H[F.vertexImage] ↾ F.edgeImage

/-- A homomorphism is surjective when its image is the whole target. -/
def Surjective (F : Hom G H) : Prop := F.Image = H

@[simp]
theorem mem_vertexImage_iff (F : Hom G H) {v : V₁} :
    v ∈ F.vertexImage ↔ ∃ x : V(G), (F.vertMap x).1 = v :=
  Iff.rfl

@[simp]
theorem mem_edgeImage_iff (F : Hom G H) {e : E₁} :
    e ∈ F.edgeImage ↔ ∃ f : E(G), (F.edgeMap f).1 = e :=
  Iff.rfl

theorem vertexImage_subset (F : Hom G H) : F.vertexImage ⊆ V(H) := by
  rintro _ ⟨x, rfl⟩
  exact (F.vertMap x).2

theorem edgeImage_subset (F : Hom G H) : F.edgeImage ⊆ E(H) := by
  rintro _ ⟨e, rfl⟩
  exact (F.edgeMap e).2

theorem image_le (F : Hom G H) : F.Image ≤ H :=
  restrict_le.trans (induce_le F.vertexImage_subset)

@[simp]
theorem image_vertexSet (F : Hom G H) : V(F.Image) = F.vertexImage := by
  simp [Image]

@[simp]
theorem image_edgeSet (F : Hom G H) : E(F.Image) = F.edgeImage := by
  rw [Image, edgeSet_restrict]
  refine inter_eq_right.mpr ?_
  rintro _ ⟨e, rfl⟩
  obtain ⟨x, y, hxy⟩ := G.exists_isLink_of_mem_edgeSet e.2
  have h := F.map_isLink (x := ⟨x, hxy.left_mem⟩) (y := ⟨y, hxy.right_mem⟩) hxy
  exact (show H[F.vertexImage].IsLink _ _ _ from
    ⟨h, ⟨⟨x, hxy.left_mem⟩, rfl⟩, ⟨⟨y, hxy.right_mem⟩, rfl⟩⟩).edge_mem

/-- The image is the least target subgraph containing both map ranges. -/
theorem image_le_iff (F : Hom G H) {L : Graph V₁ E₁} (hL : L ≤ H) :
    F.Image ≤ L ↔ F.vertexImage ⊆ V(L) ∧ F.edgeImage ⊆ E(L) := by
  refine ⟨fun h ↦ ?_, fun ⟨hV, hE⟩ ↦ le_of_le_le_subset_subset F.image_le hL hV
    (F.image_edgeSet ▸ hE)⟩
  simpa only [F.image_vertexSet, F.image_edgeSet] using
    And.intro h.vertexSet_mono h.edgeSet_mono

/-- Restrict the codomain to the image. -/
def toImage (F : Hom G H) : Hom G F.Image where
  vertMap x := ⟨(F.vertMap x).1, F.image_vertexSet ▸ ⟨x, rfl⟩⟩
  edgeMap e := ⟨(F.edgeMap e).1, F.image_edgeSet ▸ ⟨e, rfl⟩⟩
  map_isLink _ _ _ h :=
    (F.map_isLink h).of_le_of_mem F.image_le (F.image_edgeSet ▸ ⟨_, rfl⟩)

@[simp]
theorem toImage_vertMap_val (F : Hom G H) (x : V(G)) :
    (F.toImage.vertMap x).1 = (F.vertMap x).1 :=
  rfl

@[simp]
theorem toImage_edgeMap_val (F : Hom G H) (e : E(G)) :
    (F.toImage.edgeMap e).1 = (F.edgeMap e).1 :=
  rfl

theorem toImage_vertMap_surjective (F : Hom G H) :
    Function.Surjective F.toImage.vertMap := by
  rintro ⟨u, hu⟩
  obtain ⟨x, hx⟩ := F.mem_vertexImage_iff.mp (F.image_vertexSet ▸ hu)
  exact ⟨x, Subtype.ext hx⟩

theorem toImage_edgeMap_surjective (F : Hom G H) :
    Function.Surjective F.toImage.edgeMap := by
  rintro ⟨e, he⟩
  obtain ⟨f, hf⟩ := F.mem_edgeImage_iff.mp (F.image_edgeSet ▸ he)
  exact ⟨f, Subtype.ext hf⟩

/-- Corestriction followed by inclusion recovers the original homomorphism. -/
theorem toImage_comp_ofLe (F : Hom G H) :
    F.toImage.comp (Emb.ofLe F.image_le).toHom = F := by
  cases F
  rfl

theorem vertexImage_eq_iff (F : Hom G H) :
    F.vertexImage = V(H) ↔ Function.Surjective F.vertMap := by
  refine ⟨fun h ⟨x, hx⟩ ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨y, hy⟩ := F.mem_vertexImage_iff.mp (h ▸ hx)
    exact ⟨y, Subtype.ext hy⟩
  · ext x
    exact ⟨fun hx ↦ F.vertexImage_subset hx, fun hx ↦
      ⟨(h ⟨x, hx⟩).choose, congrArg Subtype.val (h ⟨x, hx⟩).choose_spec⟩⟩

theorem edgeImage_eq_iff (F : Hom G H) : F.edgeImage = E(H) ↔ Function.Surjective F.edgeMap := by
  refine ⟨fun h ⟨e, he⟩ ↦ ?_, fun h ↦ ?_⟩
  · obtain ⟨f, hf⟩ := F.mem_edgeImage_iff.mp (h ▸ he)
    exact ⟨f, Subtype.ext hf⟩
  · ext e
    exact ⟨fun he ↦ F.edgeImage_subset he, fun he ↦
      ⟨(h ⟨e, he⟩).choose, congrArg Subtype.val (h ⟨e, he⟩).choose_spec⟩⟩

/-- Exhausting the host means surjectivity on both vertex and edge sets. -/
theorem surjective_iff (F : Hom G H) :
    F.Surjective ↔ Function.Surjective F.vertMap ∧ Function.Surjective F.edgeMap := by
  change F.Image = H ↔ _
  rw [← F.vertexImage_eq_iff, ← F.edgeImage_eq_iff]
  refine ⟨fun h ↦ ?_, fun ⟨hV, hE⟩ ↦ ?_⟩
  · exact ⟨F.image_vertexSet.symm.trans (congrArg vertexSet h),
      F.image_edgeSet.symm.trans (congrArg edgeSet h)⟩
  · exact ext_of_le_le F.image_le le_rfl
      (F.image_vertexSet.trans hV) (F.image_edgeSet.trans hE)

theorem Surjective.vertMap {F : Hom G H} (hF : F.Surjective) :
    Function.Surjective F.vertMap := (F.surjective_iff.mp hF).1

theorem Surjective.edgeMap {F : Hom G H} (hF : F.Surjective) :
    Function.Surjective F.edgeMap := (F.surjective_iff.mp hF).2

/-- Corestriction to the image is surjective. -/
@[simp]
theorem toImage_surjective (F : Hom G H) : F.toImage.Surjective :=
  F.toImage.surjective_iff.mpr ⟨F.toImage_vertMap_surjective, F.toImage_edgeMap_surjective⟩

@[simp]
theorem image_ofLe {G H : Graph V₀ E₀} (h : G ≤ H) :
    (Emb.ofLe h).toHom.Image = G := by
  apply ext_of_le_le (Emb.ofLe h).toHom.image_le h
  · simp [vertexImage]
  · simp [edgeImage]

@[simp]
theorem image_toHom (F : Iso G H) : F.toHom.Image = H :=
  (F.surjective_iff).2 ⟨F.vertEquiv.surjective, F.edgeEquiv.surjective⟩

/-- Precomposition can only decrease the image, with no injectivity assumptions. -/
theorem image_comp_le (F : Hom G H) (F' : Hom H K) :
    (F.comp F').Image ≤ F'.Image := by
  apply (image_le_iff _ F'.image_le).2
  constructor
  · rintro _ ⟨x, rfl⟩
    exact F'.image_vertexSet ▸ ⟨F.vertMap x, rfl⟩
  · rintro _ ⟨e, rfl⟩
    exact F'.image_edgeSet ▸ ⟨F.edgeMap e, rfl⟩

/-- The image of a composite depends only on the first homomorphism's image. -/
theorem image_comp (F : Hom G H) (F' : Hom H K) :
    (F.comp F').Image = ((Emb.ofLe F.image_le).toHom.comp F').Image := by
  apply ext_of_le_le (F.comp F').image_le
    ((Emb.ofLe F.image_le).toHom.comp F').image_le
  · -- Reindex the vertex range using the surjective corestriction of F.
    simp only [image_vertexSet, vertexImage, comp_vertMap, comp_apply, range_comp',
      image_val_inj]
    congr 1
    rw [← image_val_inj, ← image_univ, image_image, ← image_univ, image_image]
    simp only [coe_ofLe_vertMap, image_univ, Subtype.range_val]
    rfl
  · -- The same range-composition argument applies independently to the edge map.
    simp only [image_edgeSet, edgeImage, comp_edgeMap, comp_apply,
      range_comp', image_val_inj]
    congr 1
    rw [← image_val_inj, ← image_univ, image_image, ← image_univ, image_image]
    simp only [coe_ofLe_edgeMap, image_univ, Subtype.range_val, image_edgeSet]
    rfl

end Hom

namespace Emb

/-- The isomorphism from the source onto the image of the embedding. -/
noncomputable def isoImage (F : Emb G H) : Iso G F.Image :=
  Iso.ofBijective F.toImage
    ⟨fun _ _ h ↦ F.vertMap_injective
      (Subtype.ext (congrArg (fun x : V(F.Image) ↦ x.1) h)),
      F.toImage_vertMap_surjective⟩
    ⟨fun _ _ h ↦ F.edgeMap_injective
      (Subtype.ext (congrArg (fun e : E(F.Image) ↦ e.1) h)),
      F.toImage_edgeMap_surjective⟩

@[simp]
theorem isoImage_vertMap_val (F : Emb G H) (x : V(G)) :
    (F.isoImage.vertMap x).1 = (F.vertMap x).1 := rfl

@[simp]
theorem isoImage_edgeMap_val (F : Emb G H) (e : E(G)) :
    (F.isoImage.edgeMap e).1 = (F.edgeMap e).1 := rfl

/-- Factoring an embedding through its image preserves the original embedding. -/
theorem isoImage_comp_ofLe (F : Emb G H) :
    F.isoImage.toEmb.comp (Emb.ofLe F.image_le) = F := by
  cases F
  rfl

end Emb

/-- An isomorphism is surjective. -/
@[simp]
theorem Iso.surjective (F : Iso G H) : F.Surjective :=
  Hom.image_toHom F

end Graph
