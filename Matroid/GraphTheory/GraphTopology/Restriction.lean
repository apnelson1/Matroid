module

public import Matroid.GraphLike.Basic

/-! # Restrictions and finite supports of graph-like spaces

Selections are raw sets, normalized against the vertices and edges of the graph.
A restriction retains selected whole edges, their endpoints, and requested vertices.
-/

@[expose] public section

open Set Function TopologicalSpace Topology Set.Notation

namespace GraphLike

variable {X : Type*} [TopologicalSpace X] (G : GraphLike X) (A : Set X) (B : Set (Set X))

/-- The selected vertices and selected whole edges, clipped to the graph. -/
def support : Set X := (A ∩ V(G)) ∪ ⋃₀ (B ∩ E(G))

/-- Vertices retained by a restriction, including selected edge endpoints. -/
def restrictVertices : Set X := G.support A B ∩ V(G)

lemma support_subset : G.support A B ⊆ G.carrier := by
  rintro x (hx | hx)
  · exact G.subset hx.2
  · obtain ⟨e, he, hx⟩ := mem_sUnion.mp hx
    exact G.edge_subset he.2 hx

lemma edge_subset_support {e : Set X} (he : e ∈ E(G)) (hB : e ∈ B) :
    e ⊆ G.support A B := fun _ hx ↦ Or.inr (mem_sUnion.mpr ⟨e, ⟨hB, he⟩, hx⟩)

lemma vertices_eq : G.restrictVertices A B =
    (A ∩ V(G)) ∪ ⋃ e ∈ B ∩ E(G), G.edgeBoundary e := by
  ext x
  simp only [restrictVertices, support, edgeBoundary, mem_inter_iff, mem_union,
    mem_sUnion, mem_iUnion]
  aesop

lemma interior_inter_support {e : Set X} (he : e ∈ E(G)) :
    G.edgeInterior e ∩ G.support A B = {x ∈ G.edgeInterior e | e ∈ B} := by
  ext x
  constructor
  · rintro ⟨hx, hv | hy⟩
    · exact False.elim (hx.2 hv.2)
    · obtain ⟨f, hf, hxf⟩ := mem_sUnion.mp hy
      have hef := G.edge_eq_of_mem_edgeInterior he hf.2 hx ⟨hxf, hx.2⟩
      exact ⟨hx, hef ▸ hf.1⟩
  · rintro ⟨hx, hB⟩
    exact ⟨hx, G.edge_subset_support A B he hB hx.1⟩

lemma edge_subset_support_iff {e : Set X} (he : e ∈ E(G)) :
    e ⊆ G.support A B ↔ e ∈ B := by
  refine ⟨fun h ↦ ?_, G.edge_subset_support A B he⟩
  obtain ⟨x, hx⟩ := G.edgeInterior_nonempty he
  have hm : x ∈ G.edgeInterior e ∩ G.support A B := ⟨hx, h hx.1⟩
  rw [G.interior_inter_support A B he] at hm
  exact hm.2

private lemma support_diff_vertices :
    G.support A B \ G.restrictVertices A B =
      ⋃ e : ↥(B ∩ E(G)), G.edgeInterior e.1 := by
  ext x
  constructor
  · rintro ⟨hx, hv⟩
    have hxv : x ∉ V(G) := fun h ↦ hv ⟨hx, h⟩
    rcases hx with hx | hx
    · exact False.elim (hxv hx.2)
    obtain ⟨e, he, hx⟩ := mem_sUnion.mp hx
    exact mem_iUnion.mpr ⟨⟨e, he⟩, hx, hxv⟩
  · intro hx
    obtain ⟨e, he⟩ := mem_iUnion.mp hx
    exact ⟨G.edge_subset_support A B e.2.2 e.2.1 he.1, fun hv ↦ he.2 hv.2⟩

private theorem restriction_components :
    ∃ q : ↥(B ∩ E(G)) ≃ ConnectedComponents ↥(G.support A B \ G.restrictVertices A B),
      ∀ e, Subtype.val '' (q e).toSet = G.edgeInterior e.1 := by
  classical
  let S := G.support A B \ G.restrictVertices A B
  let U (e : ↥(B ∩ E(G))) : Set S := Subtype.val ⁻¹' G.edgeInterior e.1
  have hsub (e : ↥(B ∩ E(G))) : G.edgeInterior e.1 ⊆ S := by
    rw [show S = _ from G.support_diff_vertices A B]
    exact fun x hx ↦ mem_iUnion.mpr ⟨e, hx⟩
  have himage (e : ↥(B ∩ E(G))) : Subtype.val '' U e = G.edgeInterior e.1 := by
    exact image_preimage_eq_inter_range.trans (by
      rw [Subtype.range_coe, inter_eq_left.mpr (hsub e)])
  have hdisj : Pairwise (Disjoint on U) := by
    intro e f hef
    exact (G.edgeInterior_disjoint e.2.2 f.2.2 (fun h ↦ hef (Subtype.ext h))).preimage _
  have hcover : ⋃ e, U e = univ := by
    apply eq_univ_of_forall
    intro x
    have hx : x.1 ∈ ⋃ e : ↥(B ∩ E(G)), G.edgeInterior e.1 :=
      (G.support_diff_vertices A B).subset x.2
    simpa only [mem_iUnion, U, mem_preimage] using hx
  have hopen (e : ↥(B ∩ E(G))) : IsOpen (U e) :=
    (G.interior_isOpen e.2.2).preimage
      (continuous_subtype_val.subtype_mk fun x : S ↦ G.support_subset A B x.2.1)
  have hclopen (e : ↥(B ∩ E(G))) : IsClopen (U e) := by
    have hc : (U e)ᶜ = ⋃ f : {f // f ≠ e}, U f := by
      simpa [iUnion_subtype] using
        biUnion_compl_eq_of_pairwise_disjoint_of_iUnion_eq_univ hcover hdisj {e}
    refine ⟨isOpen_compl_iff.mp ?_, hopen e⟩
    rw [hc]
    exact isOpen_iUnion fun f ↦ hopen f.1
  have hconn (e : ↥(B ∩ E(G))) : IsConnected (U e) := by
    refine ⟨?_, IsInducing.subtypeVal.isPreconnected_image.mp ?_⟩
    · rw [← image_nonempty, himage]
      exact G.edgeInterior_nonempty e.2.2
    · rw [himage]
      exact (G.edgeInterior_isConnected e.2.2).isPreconnected
  refine ⟨(ConnectedComponents.equivOfIsClopenOfIsConnected
    hclopen hdisj hcover hconn).symm, fun e ↦ ?_⟩
  rw [ConnectedComponents.toSet,
    ConnectedComponents.preimage_singleton_equivOfIsClopenOfIsConnected_symm]
  exact himage e

private noncomputable def restrictionComponents := (G.restriction_components A B).choose

private lemma restrictionComponents_interior (e : ↥(B ∩ E(G))) :
    Subtype.val '' (G.restrictionComponents A B e).toSet =
      G.edgeInterior e.1 := (G.restriction_components A B).choose_spec e

private lemma restrictionComponents_range (e : ↥(B ∩ E(G))) :
    G.support A B ∩ closure
      (Subtype.val '' (G.restrictionComponents A B e).toSet) =
      e.1 := by
  rw [G.restrictionComponents_interior]
  apply subset_antisymm
  · exact (inter_subset_inter_left _ (G.support_subset A B)).trans
      (G.edge_eq_inter_closure_edgeInterior e.2.2).subset
  · exact fun x hx ↦ ⟨G.edge_subset_support A B e.2.2 e.2.1 hx,
      G.edge_subset_closure_edgeInterior e.2.2 hx⟩

/-- Restrict to selected whole edges and requested vertices, retaining edge endpoints. -/
noncomputable def restrict : GraphLike X where
  carrier := G.support A B
  vertexSet := G.restrictVertices A B
  t2Space := (IsEmbedding.inclusion (G.support_subset A B)).t2Space
  subset := inter_subset_left
  isClosed := by
    have h := G.isClosed.preimage (continuous_inclusion (G.support_subset A B))
    convert h using 1
    ext x
    exact and_iff_right x.2
  isTotallySeparated := by
    let f := Set.inclusion (G.support_subset A B)
    intro x hx y hy hxy
    obtain ⟨U, V, hU, hV, hxU, hyV, hcover, hd⟩ :=
      G.isTotallySeparated (x := f x) (y := f y) hx.2 hy.2
        (fun h ↦ hxy (Set.inclusion_injective (G.support_subset A B) h))
    exact ⟨f ⁻¹' U, f ⁻¹' V, hU.preimage (continuous_inclusion _),
      hV.preimage (continuous_inclusion _), hxU, hyV,
      fun z hz ↦ hcover hz.2, hd.preimage f⟩
  interior_isOpen' := by
    intro C
    obtain ⟨e, rfl⟩ := (G.restrictionComponents A B).surjective C
    rw [G.restrictionComponents_interior]
    exact (G.interior_isOpen e.2.2).preimage (continuous_inclusion (G.support_subset A B))
  boundary_isPair' := by
    intro C
    obtain ⟨e, rfl⟩ := (G.restrictionComponents A B).surjective C
    dsimp only
    rw [G.restrictionComponents_range, G.restrictionComponents_interior]
    obtain ⟨x, hxV, y, hyV, hb, hl⟩ := G.boundary_isPair e.2.2
    have hx : x ∈ e.1 := (show x ∈ G.edgeBoundary e.1 from hb.symm ▸ (by simp)).1
    have hy : y ∈ e.1 := (show y ∈ G.edgeBoundary e.1 from hb.symm ▸ (by simp)).1
    refine ⟨⟨x, G.edge_subset_support A B e.2.2 e.2.1 hx, hxV⟩,
      ⟨y, G.edge_subset_support A B e.2.2 e.2.1 hy, hyV⟩, ?_, hl⟩
    simpa only [edgeInterior, sdiff_sdiff_right_self, edgeBoundary] using hb

@[simp] lemma restrict_carrier : (G.restrict A B).carrier = G.support A B := rfl
@[simp] lemma restrict_vertexSet : V(G.restrict A B) = G.restrictVertices A B := rfl

@[simp] lemma restrict_edgeSet : E(G.restrict A B) = B ∩ E(G) := by
  ext e
  constructor
  · rintro ⟨c, rfl⟩
    obtain ⟨d, rfl⟩ := (G.restrictionComponents A B).surjective c
    change G.support A B ∩ closure
      (Subtype.val '' (G.restrictionComponents A B d).toSet) ∈ B ∩ E(G)
    rw [G.restrictionComponents_range]
    exact d.2
  · intro he
    exact ⟨G.restrictionComponents A B ⟨e, he⟩,
      G.restrictionComponents_range A B ⟨e, he⟩⟩

@[simp] lemma restrict_edgeInterior {e : Set X} (he : e ∈ E(G)) (hB : e ∈ B) :
    (G.restrict A B).edgeInterior e = G.edgeInterior e := by
  ext x
  change (x ∈ e ∧ ¬ (x ∈ G.support A B ∧ x ∈ V(G))) ↔ x ∈ e ∧ x ∉ V(G)
  have h := G.edge_subset_support A B he hB
  aesop

@[simp] lemma restrict_edgeBoundary {e : Set X} (he : e ∈ E(G)) (hB : e ∈ B) :
    (G.restrict A B).edgeBoundary e = G.edgeBoundary e := by
  ext x
  change (x ∈ e ∧ x ∈ G.support A B ∧ x ∈ V(G)) ↔ x ∈ e ∧ x ∈ V(G)
  have h := G.edge_subset_support A B he hB
  aesop

lemma restrict_eq_iff {C : Set X} {D : Set (Set X)} :
    G.restrict A B = G.restrict C D ↔ G.support A B = G.support C D := by
  refine ⟨fun h ↦ congrArg GraphLike.carrier h, fun h ↦ GraphLike.ext h ?_⟩
  exact congrArg (· ∩ V(G)) h

lemma restrict_finite_iff :
    (G.restrict A B).Finite ↔ (A ∩ V(G)).Finite ∧ (B ∩ E(G)).Finite := by
  constructor
  · intro h
    refine ⟨h.vertexSet_finite.subset (fun x hx ↦ ⟨Or.inl hx, hx.2⟩), ?_⟩
    simpa only [restrict_edgeSet] using h.edgeSet_finite
  · rintro ⟨hA, hB⟩
    refine ⟨?_, by simpa only [restrict_edgeSet] using hB⟩
    change (G.restrictVertices A B).Finite
    rw [G.vertices_eq]
    exact hA.union (hB.biUnion fun e he ↦ G.edgeBoundary_finite he.2)

@[simp] lemma support_empty : G.support ∅ ∅ = ∅ := by simp [support]

@[simp] lemma support_univ : G.support univ univ = G.carrier := by
  simpa [support] using G.carrier_eq_vertexSet_union_sUnion_edges.symm

@[simp] lemma restrict_univ : G.restrict univ univ = G := by
  apply GraphLike.ext (G.support_univ)
  change G.support univ univ ∩ V(G) = V(G)
  rw [G.support_univ, inter_eq_right.mpr G.subset]

lemma support_union (C : Set X) (D : Set (Set X)) :
    G.support (A ∪ C) (B ∪ D) = G.support A B ∪ G.support C D := by
  ext x
  simp only [support, mem_union, mem_inter_iff, mem_sUnion]
  aesop

/-- Shared endpoints are retained even for disjoint edge selections. -/
lemma support_inter (C : Set X) (D : Set (Set X)) :
    G.support A B ∩ G.support C D =
      G.support (G.support A B ∩ G.support C D) (B ∩ D) := by
  apply subset_antisymm
  · intro x hx
    by_cases hv : x ∈ V(G)
    · exact Or.inl ⟨hx, hv⟩
    obtain ⟨e, he, hxe⟩ := G.exists_edge_of_mem ⟨G.support_subset A B hx.1, hv⟩
    have heB : e ∈ B := by
      have hm : x ∈ G.edgeInterior e ∩ G.support A B := ⟨hxe, hx.1⟩
      rw [G.interior_inter_support A B he] at hm
      exact hm.2
    have heD : e ∈ D := by
      have hm : x ∈ G.edgeInterior e ∩ G.support C D := ⟨hxe, hx.2⟩
      rw [G.interior_inter_support C D he] at hm
      exact hm.2
    exact G.edge_subset_support (G.support A B ∩ G.support C D) (B ∩ D) he ⟨heB, heD⟩ hxe.1
  · rintro x (hx | hx)
    · exact hx.1
    obtain ⟨e, he, hx⟩ := mem_sUnion.mp hx
    exact ⟨G.edge_subset_support A B he.2 he.1.1 hx,
      G.edge_subset_support C D he.2 he.1.2 hx⟩

lemma support_restrict (C : Set X) (D : Set (Set X)) :
    (G.restrict A B).support C D =
      G.support (C ∩ V(G.restrict A B)) (D ∩ E(G.restrict A B)) := by
  ext x
  simp only [support, restrict_vertexSet, restrict_edgeSet, restrictVertices,
    mem_union, mem_inter_iff, mem_sUnion]
  aesop

lemma restrict_restrict (C : Set X) (D : Set (Set X)) :
    (G.restrict A B).restrict C D =
      G.restrict (C ∩ V(G.restrict A B)) (D ∩ E(G.restrict A B)) := by
  apply GraphLike.ext (G.support_restrict A B C D)
  change (G.restrict A B).support C D ∩ (G.support A B ∩ V(G)) = _
  have hsub : (G.restrict A B).support C D ⊆ G.support A B :=
    (G.restrict A B).support_subset C D
  change _ = G.support (C ∩ V(G.restrict A B)) (D ∩ E(G.restrict A B)) ∩ V(G)
  rw [← G.support_restrict A B C D, ← inter_assoc, inter_eq_left.mpr hsub]

/-- A finite selection is compact relative to the original carrier. -/
lemma isCompact_support (hA : A.Finite) (hB : B.Finite) :
    IsCompact (G.carrier ↓∩ G.support A B) := by
  apply IsInducing.subtypeVal.isCompact_preimage'
  · exact (hA.inter_of_left _).isCompact.union
      ((hB.inter_of_left _).isCompact_sUnion fun e he ↦ G.edge_isCompact he.2)
  · simpa only [Subtype.range_coe] using G.support_subset A B

/-- Closing a difference restores precisely the surviving whole edges.
Only the selection on the left must be finite; closure is relative to the carrier. -/
lemma closure_support_sdiff (A C : Set X) (B D : Set (Set X))
    (hA : A.Finite) (hB : B.Finite) :
    G.carrier ∩ closure (G.support A B \ G.support C D) =
      G.support (A \ G.support C D) (B \ D) := by
  let A' := A \ G.support C D
  have hclosed : IsClosed (G.carrier ↓∩ G.support A' (B \ D)) :=
    (G.isCompact_support A' (B \ D) hA.sdiff hB.sdiff).isClosed
  have hsub : G.support A B \ G.support C D ⊆ G.support A' (B \ D) := by
    rintro x ⟨hv | hx, hn⟩
    · exact Or.inl ⟨⟨hv.1, hn⟩, hv.2⟩
    obtain ⟨e, he, hx⟩ := mem_sUnion.mp hx
    exact G.edge_subset_support A' (B \ D) he.2
      ⟨he.1, fun hed ↦ hn (G.edge_subset_support C D he.2 hed hx)⟩ hx
  apply subset_antisymm
  · rintro x ⟨hc, hx⟩
    have hx' : (⟨x, hc⟩ : G.carrier) ∈ closure
        (G.carrier ↓∩ (G.support A B \ G.support C D)) := by
      apply closure_subtype.mpr
      simpa only [image_preimage_eq_inter_range, Subtype.range_coe,
        inter_eq_left.mpr (sdiff_subset.trans (G.support_subset A B))] using hx
    exact hclosed.closure_subset (closure_mono (preimage_mono hsub) hx')
  · rintro x (hv | hx)
    · exact ⟨G.subset hv.2, subset_closure ⟨Or.inl ⟨hv.1.1, hv.2⟩, hv.1.2⟩⟩
    obtain ⟨e, he, hx⟩ := mem_sUnion.mp hx
    refine ⟨G.edge_subset he.2 hx, closure_mono (s := G.edgeInterior e) ?_
      (G.edge_subset_closure_edgeInterior he.2 hx)⟩
    intro y hy
    refine ⟨G.edge_subset_support A B he.2 he.1.1 hy.1, ?_⟩
    intro hyD
    have hm : y ∈ G.edgeInterior e ∩ G.support C D := ⟨hy, hyD⟩
    rw [G.interior_inter_support C D he.2] at hm
    exact he.1.2 hm.2

end GraphLike
