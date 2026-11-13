module

public import Matroid.GraphTheory.GraphTopology.Basic
public import Matroid.MiniTauCeti.JCT.Topology.Circuit.Compact
public import Matroid.MiniTauCeti.JCT.Topology.SeparatedUnion

/-! # Intrinsic circuits in graphlike spaces and their edge sets -/

@[expose] public section

open Set Topology Function Set.Notation

namespace GraphLike

variable {X : Type*} [TopologicalSpace X] {G : GraphLike X} {K : Set X}

/-- Missing closure points of an intrinsic circuit in a graphlike carrier are vertices.
Closure is taken inside the Hausdorff carrier. -/
theorem closure_diff_subset_vertexSet_of_isCircuit (G : GraphLike X) (hK : IsCircuit K)
    (hKG : K ⊆ G.carrier) :
    closure (G.carrier ↓∩ K) \ (G.carrier ↓∩ K) ⊆ G.carrier ↓∩ V(G) := by
  have hK' : IsCircuit (G.carrier ↓∩ K) := (isCircuit_preimage_subtypeVal_iff hKG).mpr hK
  rintro x ⟨hxcl, hxnot⟩
  by_contra hxV
  obtain ⟨e, he, hxe⟩ := G.exists_edge_of_mem ⟨x.property, hxV⟩
  obtain ⟨f, hopen, hrange⟩ := G.exists_isOpenEmbedding_edgeInterior he
  have hc := hK'.isClosed_preimage_of_isOpenEmbedding hopen
  obtain ⟨t, rfl⟩ := hrange.symm ▸ (show x ∈ G.carrier ↓∩ G.edgeInterior e from hxe)
  have ht : t ∈ closure (f ⁻¹' (G.carrier ↓∩ K)) :=
    hopen.isOpenMap.preimage_closure_subset_closure_preimage hxcl
  rw [hc.closure_eq] at ht
  exact hxnot ht

/-- Every intrinsic circuit contained in a compact graphlike carrier is compact.
The ambient space need not be Hausdorff, and the graphlike space may be infinite or disconnected. -/
theorem isCompact_of_isCircuit_subset (G : GraphLike X) (hG : IsCompact G.carrier)
    (hK : IsCircuit K) (hKG : K ⊆ G.carrier) : IsCompact K := by
  let : CompactSpace G.carrier := isCompact_iff_compactSpace.mp hG
  have hK' : IsCircuit (G.carrier ↓∩ K) := (isCircuit_preimage_subtypeVal_iff hKG).mpr hK
  have hc := hK'.isCompact_of_closure_diff_subset isClosed_closure.isCompact G.isClosed
    G.isTotallySeparated.isTotallyDisconnected (G.closure_diff_subset_vertexSet_of_isCircuit hK hKG)
  simpa only [Subtype.image_preimage_coe, inter_eq_right.mpr hKG] using
    hc.image continuous_subtype_val

variable {e : Set X}

/-- An intrinsic circuit meeting an edge interior contains that entire interior. -/
theorem edgeInterior_subset_of_isCircuit (G : GraphLike X) (hK : IsCircuit K)
    (hKG : K ⊆ G.carrier) (he : e ∈ E(G)) (hne : (K ∩ G.edgeInterior e).Nonempty) :
    G.edgeInterior e ⊆ K := by
  have hK' := (isCircuit_preimage_subtypeVal_iff hKG).mpr hK
  obtain ⟨f, hf, hrange⟩ := G.exists_isOpenEmbedding_edgeInterior he
  have hsub := hK'.range_subset_of_isOpenEmbedding hf (by
    obtain ⟨x, hxK, hxe⟩ := hne
    exact ⟨⟨x, hKG hxK⟩, hxK, hrange.symm ▸ hxe⟩)
  intro x hx
  exact hsub (hrange.symm ▸ (show (⟨x, G.edge_subset he hx.1⟩ : G.carrier) ∈
    G.carrier ↓∩ G.edgeInterior e from hx))

/-- An intrinsic circuit meeting an edge interior contains the whole edge. -/
theorem edge_subset_of_isCircuit (G : GraphLike X) (hK : IsCircuit K)
    (hKG : K ⊆ G.carrier) (he : e ∈ E(G)) (hne : (K ∩ G.edgeInterior e).Nonempty) :
    e ⊆ K := by
  have hK' := (isCircuit_preimage_subtypeVal_iff hKG).mpr hK
  obtain ⟨a, _, b, _, hb, hl⟩ := G.boundary_isPair he
  obtain ⟨P, hP, hPrange⟩ := hl.restrictSubtype (G.edge_subset he)
  have hint : P.Interior = G.carrier ↓∩ G.edgeInterior e := by
    rw [← hP.range_diff_endpoints, hPrange]
    ext z
    have hz : z.val ∈ e ∩ V(G) ↔ z.val = a ∨ z.val = b := by
      change z.val ∈ G.edgeBoundary e ↔ _
      rw [hb]
      rfl
    simp only [mem_sdiff, mem_preimage, mem_insert_iff, mem_singleton_iff, Subtype.ext_iff,
      edgeInterior]
    simp only [mem_inter_iff] at hz
    tauto
  have hsub := hK'.range_subset_of_isPrimitive hP
    (hint.symm ▸ G.interior_isOpen he) (by
      obtain ⟨x, hxK, hxe⟩ := hne
      exact ⟨⟨x, hKG hxK⟩, hxK, hint.symm ▸ hxe⟩)
  intro x hx
  exact hsub (hPrange.symm ▸ (show (⟨x, G.edge_subset he hx⟩ : G.carrier) ∈
    G.carrier ↓∩ e from hx))

/-- Nonvertices are dense in any nontrivial compact connected subset of the carrier. -/
theorem subset_closure_sdiff_vertexSet_of_isPreconnected (G : GraphLike X)
    (hK : IsPreconnected K) (hne : K.Nontrivial) (hc : IsCompact K)
    (hKG : K ⊆ G.carrier) : K ⊆ closure (K \ V(G)) := by
  let : T2Space K := (IsEmbedding.inclusion hKG).t2Space
  let : CompactSpace K := isCompact_iff_compactSpace.mp hc
  let : PreconnectedSpace K := isPreconnected_iff_preconnectedSpace.mp hK
  let : Nontrivial K := nontrivial_coe_sort.mpr hne
  have hclosed : IsClosed (K ↓∩ V(G)) :=
    G.isClosed.preimage (continuous_inclusion hKG)
  have htd : IsTotallyDisconnected (K ↓∩ V(G)) := by
    apply (IsEmbedding.inclusion hKG).isTotallyDisconnected
    intro C hC hconn
    exact G.isTotallySeparated.isTotallyDisconnected C (hC.trans (by
      rintro _ ⟨x, hx, rfl⟩
      exact hx)) hconn
  have hdense := interior_eq_empty_iff_dense_compl.mp
    (htd.interior_eq_empty_of_isCompact hclosed.isCompact)
  intro x hx
  have hm := hdense (⟨x, hx⟩ : K)
  rw [closure_subtype] at hm
  apply closure_mono _ hm
  rintro _ ⟨y, hy, rfl⟩
  exact ⟨y.2, hy⟩

/-- A compact intrinsic circuit is recovered from the edges it contains by closure
relative to the carrier, without an ambient separation assumption. -/
theorem isCircuit_eq_inter_closure_edges (G : GraphLike X) (hK : IsCircuit K)
    (hc : IsCompact K) (hKG : K ⊆ G.carrier) :
    K = G.carrier ∩ closure (⋃₀ {e : Set X | e ∈ E(G) ∧ e ⊆ K}) := by
  have hclosed : IsClosed (G.carrier ↓∩ K) :=
    (IsInducing.subtypeVal.isCompact_preimage' hc (by simpa using hKG)).isClosed
  apply subset_antisymm
  · intro x hx
    refine ⟨hKG hx, closure_mono ?_
      (G.subset_closure_sdiff_vertexSet_of_isPreconnected hK.isConnected.isPreconnected
        hK.nontrivial hc hKG hx)⟩
    intro y hy
    obtain ⟨e, he, hye⟩ := G.exists_edge_of_mem ⟨hKG hy.1, hy.2⟩
    exact mem_sUnion.mpr ⟨e, ⟨he, G.edge_subset_of_isCircuit hK hKG he
      ⟨y, hy.1, hye⟩⟩, hye.1⟩
  · rintro x ⟨hxG, hx⟩
    apply hclosed.closure_subset (a := ⟨x, hxG⟩)
    apply closure_subtype.mpr
    simp only [Subtype.image_preimage_coe, inter_eq_right.mpr hKG]
    exact closure_mono (sUnion_subset fun e (he : e ∈ E(G) ∧ e ⊆ K) ↦ he.2) hx

/-- A connected nontrivial subset meeting only finitely many edge interiors is contained
in the union of those edges. No compactness assumption on the carrier is needed. -/
theorem subset_sUnion_edges_of_isPreconnected (G : GraphLike X)
    (hK : IsPreconnected K) (hne : K.Nontrivial) (hKG : K ⊆ G.carrier)
    {F : Set (Set X)} (hF : F.Finite) (hFE : F ⊆ E(G))
    (hcover : K \ V(G) ⊆ ⋃₀ F) : K ⊆ ⋃₀ F := by
  let A : Set G.carrier := Subtype.val ⁻¹' ⋃₀ F
  let V : Set G.carrier := Subtype.val ⁻¹' V(G)
  have hAG : ⋃₀ F ⊆ G.carrier := sUnion_subset fun e he ↦ G.edge_subset (hFE he)
  have hcA : IsCompact A := IsInducing.subtypeVal.isCompact_iff.mpr (by
    simpa only [A, Subtype.image_preimage_coe, inter_eq_right.mpr hAG] using
      hF.isCompact_sUnion (fun e he ↦ G.edge_isCompact (hFE he)))
  have hAV : (A ∩ V).Finite := by
    have hf : (⋃₀ F ∩ V(G)).Finite := by
      have heq : ⋃₀ F ∩ V(G) = ⋃ e ∈ F, G.edgeBoundary e := by
        ext x
        simp only [mem_inter_iff, mem_sUnion, mem_iUnion, edgeBoundary]
        aesop
      rw [heq]
      exact hF.biUnion (fun e he ↦ G.edgeBoundary_finite (hFE he))
    exact hf.preimage Subtype.val_injective.injOn
  have hK' : IsPreconnected (G.carrier ↓∩ K) :=
    IsInducing.subtypeVal.isPreconnected_image.mp (by
      simpa only [Subtype.image_preimage_coe, inter_eq_right.mpr hKG] using hK)
  obtain ⟨y, hyK, hyV⟩ : ∃ y ∈ K, y ∉ V(G) := by
    by_contra! h
    have hs : (G.carrier ↓∩ K).Subsingleton :=
      G.isTotallySeparated.isTotallyDisconnected _ (fun x hx ↦ h x hx) hK'
    obtain ⟨a, ha, b, hb, hab⟩ := hne
    exact hab (congrArg Subtype.val (hs (show (⟨a, hKG ha⟩ : G.carrier) ∈ _ from ha)
      (show (⟨b, hKG hb⟩ : G.carrier) ∈ _ from hb)))
  intro p hp
  by_contra hpA
  have hpV : p ∈ V(G) := by by_contra hpV; exact hpA (hcover ⟨hp, hpV⟩)
  obtain ⟨U, W, hU, hW, hpU, hAVW, hVW, hd⟩ :=
    G.isTotallySeparated.exists_separation_of_isCompact hAV.isCompact inter_subset_right
      (show (⟨p, hKG hp⟩ : G.carrier) ∈ V from hpV) (fun h ↦ hpA h.1)
  have hclosed : IsClosed (U ∩ V) := by
    have heq : U ∩ V = V \ W := by
      ext x
      constructor
      · exact fun h ↦ ⟨h.2, hd.notMem_of_mem_left h.1⟩
      · exact fun h ↦ ⟨(hVW h.1).resolve_right h.2, h.1⟩
    rw [heq]
    exact G.isClosed.sdiff hW
  have heq : (G.carrier ↓∩ K) ∩ (U \ A) = (G.carrier ↓∩ K) ∩ (U ∩ V) := by
    ext x
    constructor
    · rintro ⟨hx, hxu, hxa⟩
      refine ⟨hx, hxu, ?_⟩
      by_contra hxv
      exact hxa (hcover ⟨hx, hxv⟩)
    rintro ⟨hx, hxu, hxv⟩
    exact ⟨hx, hxu, fun hxa ↦ hd.notMem_of_mem_left hxu (hAVW ⟨hxa, hxv⟩)⟩
  obtain ⟨z, hzK, hzO, hzN⟩ := hK' (U \ A) (U ∩ V)ᶜ
    (hU.sdiff hcA.isClosed) hclosed.isOpen_compl (by
      intro x hx
      by_cases h : x ∈ U ∩ V
      · exact Or.inl ((heq.symm ▸ (show x ∈ (G.carrier ↓∩ K) ∩ (U ∩ V) from ⟨hx, h⟩)).2)
      · exact Or.inr h)
    ⟨⟨p, hKG hp⟩, hp, hpU, hpA⟩
    ⟨⟨y, hKG hyK⟩, hyK, fun h ↦ hyV h.2⟩
  exact hzN ((heq ▸ (show z ∈ (G.carrier ↓∩ K) ∩ (U \ A) from ⟨hzK, hzO⟩)).2)

/-- An intrinsic circuit with finite edge support is the union of its edges. -/
theorem isCircuit_eq_sUnion_edges_of_finite (G : GraphLike X) (hK : IsCircuit K)
    (hKG : K ⊆ G.carrier) (hF : {e | e ∈ E(G) ∧ e ⊆ K}.Finite) :
    K = ⋃₀ {e | e ∈ E(G) ∧ e ⊆ K} := by
  have hsub := G.subset_sUnion_edges_of_isPreconnected hK.isPreconnected hK.nontrivial hKG
    hF (fun _ he ↦ he.1) (by
      intro p hp
      obtain ⟨e, he, hpe⟩ := G.exists_edge_of_mem ⟨hKG hp.1, hp.2⟩
      exact mem_sUnion.mpr ⟨e, ⟨he, G.edge_subset_of_isCircuit hK hKG he ⟨p, hp.1, hpe⟩⟩,
        hpe.1⟩)
  exact hsub.antisymm (sUnion_subset fun _ he ↦ he.2)

/-- An intrinsic circuit with finitely many geometric edges is compact. -/
theorem isCompact_of_isCircuit_of_finite_edges (G : GraphLike X) (hK : IsCircuit K)
    (hKG : K ⊆ G.carrier) (hF : {e | e ∈ E(G) ∧ e ⊆ K}.Finite) : IsCompact K := by
  rw [G.isCircuit_eq_sUnion_edges_of_finite hK hKG hF]
  exact hF.isCompact_sUnion (fun _ he ↦ G.edge_isCompact he.1)

/-- The geometric edge set of an intrinsic circuit in the carrier. -/
def IsCircuitSet (G : GraphLike X) (C : Set (Set X)) : Prop :=
  ∃ K ⊆ G.carrier, IsCircuit K ∧ C = {e | e ∈ E(G) ∧ e ⊆ K}

lemma IsCircuitSet.subset {C : Set (Set X)} (hC : G.IsCircuitSet C) : C ⊆ E(G) := by
  obtain ⟨K, hKG, hK, rfl⟩ := hC
  exact fun _ h ↦ h.1

end GraphLike
