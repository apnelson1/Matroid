module

public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.ContinuousOn

/-! # Topological embeddings on a set

`IsEmbeddingOn f s` requires an embedding only on the subspace `s`.
The API keeps injectivity, continuity, and transport statements in the ambient spaces.
-/

@[expose] public section

open Set Function

namespace Topology

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {f f' : X → Y} {g : Y → Z} {s t : Set X} {u : Set Y} {x : X}

/-- A function is a topological embedding on a set if its domain restriction is an embedding. -/
def IsEmbeddingOn (f : X → Y) (s : Set X) : Prop := IsEmbedding (s.domRestrict f)

theorem isEmbeddingOn_iff_isEmbedding_domRestrict :
    IsEmbeddingOn f s ↔ IsEmbedding (s.domRestrict f) := Iff.rfl

theorem IsEmbedding.isEmbeddingOn (hf : IsEmbedding f) (s : Set X) : IsEmbeddingOn f s :=
  hf.comp IsEmbedding.subtypeVal

namespace IsEmbeddingOn

theorem isEmbedding (hf : IsEmbeddingOn f s) : IsEmbedding (s.domRestrict f) := hf

theorem injOn (hf : IsEmbeddingOn f s) : InjOn f s :=
  injOn_iff_injective.mpr hf.isEmbedding.injective

theorem continuousOn (hf : IsEmbeddingOn f s) : ContinuousOn f s :=
  continuousOn_iff_continuous_domRestrict.mpr hf.isEmbedding.continuous

protected theorem id (s : Set X) : IsEmbeddingOn id s := IsEmbedding.subtypeVal

theorem mono (hf : IsEmbeddingOn f s) (ht : t ⊆ s) : IsEmbeddingOn f t :=
  hf.isEmbedding.comp (IsEmbedding.inclusion ht)

theorem congr (hf : IsEmbeddingOn f s) (h : EqOn f f' s) : IsEmbeddingOn f' s := by
  change IsEmbedding (s.domRestrict f')
  rw [← domRestrict_eq_domRestrict_iff.mpr h]
  exact hf.isEmbedding

theorem comp (hg : IsEmbeddingOn g u) (hf : IsEmbeddingOn f s) (hfu : MapsTo f s u) :
    IsEmbeddingOn (g ∘ f) s :=
  hg.isEmbedding.comp (hf.isEmbedding.codRestrict u (fun x ↦ hfu x.2))

theorem comp_image (hg : IsEmbeddingOn g (f '' s)) (hf : IsEmbeddingOn f s) :
    IsEmbeddingOn (g ∘ f) s :=
  hg.comp hf (mapsTo_image f s)

/-- An embedding on a set identifies that subspace with its image. -/
noncomputable def homeomorphImage (hf : IsEmbeddingOn f s) : s ≃ₜ ↥(f '' s) :=
  hf.isEmbedding.toHomeomorph.trans (.setCongr (range_domRestrict f s))

@[simp] theorem homeomorphImage_apply (hf : IsEmbeddingOn f s) (x : s) :
    (hf.homeomorphImage x).1 = f x.1 := rfl

theorem homeomorphImage_symm_apply (hf : IsEmbeddingOn f s) (y : f '' s) :
    f (hf.homeomorphImage.symm y).1 = y.1 :=
  congrArg Subtype.val (hf.homeomorphImage.apply_symm_apply y)

@[simp] theorem homeomorphImage_preimage_image (hf : IsEmbeddingOn f s) (ht : t ⊆ s) :
    hf.homeomorphImage ⁻¹' (Subtype.val ⁻¹' (f '' t)) = (Subtype.val ⁻¹' t : Set s) := by
  ext x
  change f x.1 ∈ f '' t ↔ x.1 ∈ t
  exact ⟨fun ⟨y, hy, heq⟩ ↦ (hf.injOn (ht hy) x.2 heq) ▸ hy, fun hx ↦ mem_image_of_mem f hx⟩

@[simp] theorem homeomorphImage_image (hf : IsEmbeddingOn f s) (ht : t ⊆ s) :
    hf.homeomorphImage '' (Subtype.val ⁻¹' t) = (Subtype.val ⁻¹' (f '' t) : Set (f '' s)) := by
  rw [← hf.homeomorphImage_preimage_image ht]
  exact hf.homeomorphImage.surjective.image_preimage _

/-- Closure is preserved relative to the domain and its image, without ambient closedness. -/
theorem image_relative_closure (hf : IsEmbeddingOn f s) (ht : t ⊆ s) :
    f '' (s ∩ closure t) = (f '' s) ∩ closure (f '' t) := by
  have hpre := hf.homeomorphImage.preimage_closure (Subtype.val ⁻¹' (f '' t))
  simp only [IsEmbedding.subtypeVal.closure_eq_preimage_closure_image, Subtype.image_preimage_coe,
    inter_eq_right.mpr (image_mono ht), hf.homeomorphImage_preimage_image ht, Set.ext_iff,
    inter_eq_right.mpr ht] at hpre
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hcl⟩, rfl⟩
    exact ⟨mem_image_of_mem f hx, (hpre ⟨x, hx⟩).mpr hcl⟩
  rintro ⟨⟨x, hx, rfl⟩, hy⟩
  exact ⟨x, ⟨hx, (hpre ⟨x, hx⟩).mp hy⟩, rfl⟩

theorem isPreconnected_image (hf : IsEmbeddingOn f s) (ht : t ⊆ s) :
    IsPreconnected (f '' t) ↔ IsPreconnected t := by
  have h := hf.isEmbedding.isInducing.isPreconnected_image (s := Subtype.val ⁻¹' t)
  rwa [image_domRestrict, inter_eq_left.mpr ht, ← IsInducing.subtypeVal.isPreconnected_image,
    Subtype.image_preimage_coe, inter_eq_right.mpr ht] at h

theorem isConnected_image (hf : IsEmbeddingOn f s) (ht : t ⊆ s) :
    IsConnected (f '' t) ↔ IsConnected t :=
  image_nonempty.and (hf.isPreconnected_image ht)

/-- Components are preserved for points in the embedding domain, including points outside `t`. -/
theorem image_connectedComponentIn (hf : IsEmbeddingOn f s) (ht : t ⊆ s) (hx : x ∈ s) :
    f '' connectedComponentIn t x = connectedComponentIn (f '' t) (f x) := by
  by_cases hxt : x ∈ t
  · refine ((hf.continuousOn.mono ht).image_connectedComponentIn_subset hxt).antisymm ?_
    let C := connectedComponentIn (f '' t) (f x)
    have himage : f '' (t ∩ f ⁻¹' C) = C := by
      rw [image_inter_preimage, inter_eq_right.mpr (connectedComponentIn_subset _ _)]
    have hpre : IsPreconnected (t ∩ f ⁻¹' C) :=
      (hf.isPreconnected_image (inter_subset_left.trans ht)).mp
        (himage.symm ▸ isPreconnected_connectedComponentIn)
    have hsub := hpre.subset_connectedComponentIn
      (show x ∈ t ∩ f ⁻¹' C from
        ⟨hxt, mem_connectedComponentIn (mem_image_of_mem f hxt)⟩) inter_subset_left
    change C ⊆ f '' connectedComponentIn t x
    rw [← himage]
    exact image_mono hsub
  rw [connectedComponentIn_eq_empty hxt, image_empty, connectedComponentIn_eq_empty ?_]
  rintro ⟨y, hy, heq⟩
  exact hxt ((hf.injOn (ht hy) hx heq) ▸ hy)

/-- Embeddings preserve relative closures of components of subsets of their domain.
The point need only belong to the embedding domain, not to the subset. -/
theorem image_relative_closure_connectedComponentIn (hf : IsEmbeddingOn f s) (ht : t ⊆ s)
    (hx : x ∈ s) : f '' (s ∩ closure (connectedComponentIn t x)) =
      f '' s ∩ closure (connectedComponentIn (f '' t) (f x)) := by
  rw [hf.image_relative_closure ((connectedComponentIn_subset ..).trans ht),
    hf.image_connectedComponentIn ht hx]

end IsEmbeddingOn

@[simp] theorem isEmbeddingOn_empty (f : X → Y) : IsEmbeddingOn f ∅ :=
  IsEmbedding.of_subsingleton _

@[simp] theorem isEmbeddingOn_univ : IsEmbeddingOn f univ ↔ IsEmbedding f :=
  ⟨fun hf ↦ hf.isEmbedding.comp (Homeomorph.Set.univ X).symm.isEmbedding,
    fun hf ↦ hf.isEmbeddingOn univ⟩

end Topology
