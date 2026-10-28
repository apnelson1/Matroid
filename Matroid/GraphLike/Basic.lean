module

public import Matroid.GraphLike.Defs
public import Matroid.ForMathlib.Topology.ConnectedComponent

/-! # Edges and finite carriers of graph-like spaces -/

@[expose] public section

open Set Function TopologicalSpace Topology Set.Notation

variable {X : Type*} [TopologicalSpace X] {K : Set X} {G H : GraphLike X} {x y : X}

namespace GraphLike

@[ext]
lemma ext (hS : G.carrier = H.carrier) (hZ : G.vertexSet = H.vertexSet) : G = H := by
  cases G
  cases H
  cases hS
  cases hZ
  rfl

instance : IsPartialOrder (GraphLike X) GraphLike.finer where
  refl _ := ⟨rfl, Subset.rfl⟩
  trans _ _ _ hGH hHK := ⟨hGH.1.trans hHK.1, hGH.2.trans hHK.2⟩
  antisymm _ _ hGH hHG := ext hGH.1 (hGH.2.antisymm hHG.2)

variable (G)

/-! ## Construction correspondence

The ordinary edge API uses subsets of `X` with membership in `E(G)`. Connected components
of the vertex complement index their construction, using the general topological point-set API.
-/

@[simp] lemma componentClosure_mem_edgeSet
    (c : ConnectedComponents ↥(G.carrier \ V(G))) :
    G.carrier ∩ closure (Subtype.val '' c.toSet) ∈ E(G) := ⟨c, rfl⟩

@[simp] lemma edgeInterior_componentClosure
    (c : ConnectedComponents ↥(G.carrier \ V(G))) :
    G.edgeInterior (G.carrier ∩ closure (Subtype.val '' c.toSet)) =
      Subtype.val '' c.toSet := by
  convert c.inter_closure_image_toSet using 1
  ext x
  simp only [edgeInterior, mem_sdiff, mem_inter_iff]
  tauto

@[simp] lemma edgeBoundary_componentClosure
    (c : ConnectedComponents ↥(G.carrier \ V(G))) :
    G.edgeBoundary (G.carrier ∩ closure (Subtype.val '' c.toSet)) =
      (G.carrier ∩ closure (Subtype.val '' c.toSet)) \ (Subtype.val '' c.toSet) := by
  calc
    _ = (G.carrier ∩ closure (Subtype.val '' c.toSet)) \
        G.edgeInterior (G.carrier ∩ closure (Subtype.val '' c.toSet)) :=
      (sdiff_sdiff_right_self _ _).symm
    _ = _ := by rw [edgeInterior_componentClosure]

/-- Construction correspondence between complement components and geometric edges. -/
noncomputable def componentEdgeEquiv :
    ConnectedComponents ↥(G.carrier \ V(G)) ≃ ↥E(G) :=
  Equiv.ofInjective _ (fun c d h ↦ ConnectedComponents.toSet_injective <|
    (Set.image_injective.mpr Subtype.val_injective) <| by
      simpa only [edgeInterior_componentClosure] using congrArg G.edgeInterior h)

@[simp] lemma componentEdgeEquiv_coe (c : ConnectedComponents ↥(G.carrier \ V(G))) :
    (G.componentEdgeEquiv c).1 = G.carrier ∩ closure (Subtype.val '' c.toSet) := rfl

@[simp] lemma componentEdgeEquiv_symm_range (e : E(G)) :
    G.carrier ∩ closure (Subtype.val '' (G.componentEdgeEquiv.symm e).toSet) = e.1 :=
  congrArg Subtype.val (G.componentEdgeEquiv.apply_symm_apply e)

instance [G.Finite] : _root_.Finite (ConnectedComponents ↥(G.carrier \ V(G))) :=
  _root_.Finite.of_equiv ↥E(G) G.componentEdgeEquiv.symm

/-! ## Geometric edges -/

variable {e f : Set X}

lemma edge_subset (he : e ∈ E(G)) : e ⊆ G.carrier := by
  obtain ⟨c, rfl⟩ := he
  exact inter_subset_left

lemma edgeInterior_subset_edge (e : Set X) : G.edgeInterior e ⊆ e := sdiff_subset

lemma edgeBoundary_subset_edge (e : Set X) : G.edgeBoundary e ⊆ e := inter_subset_left

lemma edgeBoundary_subset_vertexSet (e : Set X) : G.edgeBoundary e ⊆ V(G) := inter_subset_right

lemma edgeInterior_subset (he : e ∈ E(G)) : G.edgeInterior e ⊆ G.carrier \ V(G) :=
  sdiff_subset_sdiff_left (G.edge_subset he)

lemma edgeInterior_nonempty (he : e ∈ E(G)) : (G.edgeInterior e).Nonempty := by
  obtain ⟨c, rfl⟩ := he
  rw [edgeInterior_componentClosure]
  exact c.toSet_nonempty.image _

lemma edge_nonempty (he : e ∈ E(G)) : e.Nonempty :=
  (G.edgeInterior_nonempty he).mono (G.edgeInterior_subset_edge e)

lemma edgeInterior_isConnected (he : e ∈ E(G)) : IsConnected (G.edgeInterior e) := by
  obtain ⟨c, rfl⟩ := he
  rw [edgeInterior_componentClosure]
  exact c.isConnected_toSet.image _ continuous_subtype_val.continuousOn

lemma interior_isOpen (he : e ∈ E(G)) : IsOpen (G.carrier ↓∩ G.edgeInterior e) := by
  obtain ⟨c, rfl⟩ := he
  simpa only [edgeInterior_componentClosure] using G.interior_isOpen' c

lemma boundary_isPair (he : e ∈ E(G)) :
    ∃ x ∈ V(G), ∃ y ∈ V(G), G.edgeBoundary e = {x, y} ∧ IsPrimitiveLink e x y := by
  obtain ⟨c, rfl⟩ := he
  obtain ⟨x, y, hb, hl⟩ := G.boundary_isPair' c
  exact ⟨x, x.2, y, y.2, (G.edgeBoundary_componentClosure c).trans hb, hl⟩

lemma edge_isPrimitiveLink (he : e ∈ E(G)) (hb : G.edgeBoundary e = {x, y}) :
    IsPrimitiveLink e x y := by
  obtain ⟨a, _, b, _, hab, hlink⟩ := G.boundary_isPair he
  obtain ⟨ha, hb⟩ | ⟨ha, hb⟩ := pair_eq_pair_iff.mp (hab.symm.trans hb)
  · simpa only [ha, hb] using hlink
  simpa only [ha, hb] using hlink.symm

lemma edge_isCompact (he : e ∈ E(G)) : IsCompact e := by
  obtain ⟨x, _, y, _, _, h⟩ := G.boundary_isPair he
  exact h.isCompact

lemma edgeBoundary_finite (he : e ∈ E(G)) : (G.edgeBoundary e).Finite := by
  obtain ⟨x, _, y, _, hb, _⟩ := G.boundary_isPair he
  rw [hb]
  exact (finite_singleton _).insert _

lemma edgeInterior_disjoint (he : e ∈ E(G)) (hf : f ∈ E(G)) (hne : e ≠ f) :
    Disjoint (G.edgeInterior e) (G.edgeInterior f) := by
  obtain ⟨c, rfl⟩ := he
  obtain ⟨d, rfl⟩ := hf
  rw [edgeInterior_componentClosure, edgeInterior_componentClosure]
  have hcd : c ≠ d := fun h ↦ hne (h ▸ rfl)
  refine disjoint_left.mpr ?_
  rintro _ ⟨a, ha, rfl⟩ ⟨b, hb, hab⟩
  obtain rfl := Subtype.val_injective hab
  exact (ConnectedComponents.disjoint_toSet hcd).notMem_of_mem_left ha hb

lemma edge_inter_subset_vertexSet (he : e ∈ E(G)) (hf : f ∈ E(G)) (hne : e ≠ f) :
    e ∩ f ⊆ V(G) := by
  rintro x ⟨hxe, hxf⟩
  by_contra hxV
  exact (G.edgeInterior_disjoint he hf hne).notMem_of_mem_left ⟨hxe, hxV⟩ ⟨hxf, hxV⟩

lemma edge_eq_of_edgeInterior_eq (he : e ∈ E(G)) (hf : f ∈ E(G))
    (h : G.edgeInterior e = G.edgeInterior f) : e = f := by
  by_contra hne
  obtain ⟨x, hx⟩ := G.edgeInterior_nonempty he
  exact (G.edgeInterior_disjoint he hf hne).notMem_of_mem_left hx (h ▸ hx)

lemma edge_eq_of_mem_edgeInterior (he : e ∈ E(G)) (hf : f ∈ E(G))
    (hx : x ∈ G.edgeInterior e) (hy : x ∈ G.edgeInterior f) : e = f := by
  by_contra h
  exact (G.edgeInterior_disjoint he hf h).notMem_of_mem_left hx hy

lemma edge_eq_inter_closure_edgeInterior (he : e ∈ E(G)) :
    G.carrier ∩ closure (G.edgeInterior e) = e := by
  obtain ⟨c, rfl⟩ := he
  rw [edgeInterior_componentClosure]

lemma edge_subset_closure_edgeInterior (he : e ∈ E(G)) : e ⊆ closure (G.edgeInterior e) := by
  intro x hx
  exact ((G.edge_eq_inter_closure_edgeInterior he).symm ▸ hx).2

/-- Removing an edge interior leaves a relatively closed remainder of the carrier. -/
lemma edge_isClosed_remainder (he : e ∈ E(G)) :
    IsClosed (G.carrier ↓∩ (G.carrier \ G.edgeInterior e)) := by
  convert (G.interior_isOpen he).isClosed_compl using 1
  ext x
  simp only [mem_preimage, mem_sdiff, x.property, true_and, mem_compl_iff]

lemma edge_inter_remainder (he : e ∈ E(G)) :
    e ∩ (G.carrier \ G.edgeInterior e) = G.edgeBoundary e := by
  ext x
  have := G.edge_subset he
  simp only [edgeInterior, edgeBoundary, mem_inter_iff, mem_sdiff]
  tauto

lemma edge_union_remainder (he : e ∈ E(G)) :
    e ∪ (G.carrier \ G.edgeInterior e) = G.carrier := by
  refine subset_antisymm (union_subset (G.edge_subset he) sdiff_subset) fun x hx ↦ ?_
  by_cases he : x ∈ G.edgeInterior e
  · exact Or.inl (G.edgeInterior_subset_edge e he)
  exact Or.inr ⟨hx, he⟩

/-- Deleting a set disjoint from an edge interior restores the whole edge under
closure relative to the carrier. No finiteness or ambient separation is needed. -/
lemma edge_closure_sdiff_of_disjoint_interior (he : e ∈ E(G)) {T : Set X}
    (h : Disjoint (G.edgeInterior e) T) : G.carrier ∩ closure (e \ T) = e := by
  have hs : e \ T ⊆ closure (G.edgeInterior e) :=
    fun _ hx ↦ G.edge_subset_closure_edgeInterior he hx.1
  have hi : G.edgeInterior e ⊆ e \ T :=
    fun _ hx ↦ ⟨G.edgeInterior_subset_edge e hx, h.notMem_of_mem_left hx⟩
  conv_rhs => rw [← G.edge_eq_inter_closure_edgeInterior he]
  exact subset_antisymm (fun _ hx ↦ ⟨hx.1, closure_minimal hs isClosed_closure hx.2⟩)
    (fun _ hx ↦ ⟨hx.1, closure_mono hi hx.2⟩)

lemma exists_edge_of_mem (hx : x ∈ G.carrier \ V(G)) :
    ∃ e ∈ E(G), x ∈ G.edgeInterior e := by
  let c := ConnectedComponents.mk (⟨x, hx⟩ : ↥(G.carrier \ V(G)))
  refine ⟨_, G.componentClosure_mem_edgeSet c, ?_⟩
  rw [edgeInterior_componentClosure]
  exact ⟨⟨x, hx⟩, rfl, rfl⟩

lemma carrier_eq_vertexSet_union_sUnion_edges : G.carrier = V(G) ∪ ⋃₀ E(G) := by
  refine Subset.antisymm (fun x hx ↦ ?_) ?_
  · by_cases hxV : x ∈ V(G)
    · exact Or.inl hxV
    obtain ⟨e, he, hxe⟩ := G.exists_edge_of_mem ⟨hx, hxV⟩
    exact Or.inr (mem_sUnion.mpr ⟨e, he, G.edgeInterior_subset_edge e hxe⟩)
  rintro x (hx | hx)
  · exact G.subset hx
  obtain ⟨e, he, hxe⟩ := mem_sUnion.mp hx
  exact G.edge_subset he hxe

lemma isCompact_iff_vertexSet_isCompact (hE : E(G).Finite) :
    IsCompact G.carrier ↔ IsCompact V(G) := by
  refine ⟨fun hG ↦ ?_, fun hV ↦ ?_⟩
  · have := isCompact_iff_compactSpace.mp hG
    simpa only [image_preimage_eq_inter_range, Subtype.range_coe,
      inter_eq_left.mpr G.subset] using G.isClosed.isCompact.image continuous_subtype_val
  rw [G.carrier_eq_vertexSet_union_sUnion_edges]
  exact hV.union (hE.isCompact_sUnion fun _ he ↦ G.edge_isCompact he)

lemma isCompact [G.Finite] : IsCompact G.carrier :=
  (G.isCompact_iff_vertexSet_isCompact Finite.edgeSet_finite).mpr
    Finite.vertexSet_finite.isCompact

lemma exists_edge_of_isConnected (hK : IsConnected K) (hsub : K ⊆ G.carrier \ V(G)) :
    ∃ e ∈ E(G), K ⊆ G.edgeInterior e := by
  obtain ⟨x, hx⟩ := hK.nonempty
  let x' : ↥(G.carrier \ V(G)) := ⟨x, hsub hx⟩
  refine ⟨_, G.componentClosure_mem_edgeSet (ConnectedComponents.mk x'), ?_⟩
  rw [edgeInterior_componentClosure]
  intro y hy
  refine ⟨⟨y, hsub hy⟩, ?_, rfl⟩
  rw [ConnectedComponents.mem_toSet, ConnectedComponents.coe_eq_coe']
  suffices IsPreconnected (Subtype.val ⁻¹' K : Set ↥(G.carrier \ V(G))) from
    this.subset_connectedComponent hx hy
  rw [← IsInducing.subtypeVal.isPreconnected_image, Subtype.image_preimage_coe,
    inter_eq_right.mpr hsub]
  exact hK.isPreconnected

/-- Two distinct vertices in the closure of a connected set avoiding vertices determine
its edge's boundary. -/
lemma exists_edge_of_isConnected_of_mem_closure (hK : IsConnected K)
    (hsub : K ⊆ G.carrier \ V(G)) (hxy : x ≠ y) (hx : x ∈ V(G)) (hy : y ∈ V(G))
    (hxK : x ∈ closure K) (hyK : y ∈ closure K) :
    ∃ e ∈ E(G), K ⊆ G.edgeInterior e ∧ G.edgeBoundary e = {x, y} := by
  obtain ⟨e, he, hKe⟩ := G.exists_edge_of_isConnected hK hsub
  obtain ⟨a, _, b, _, hb, _⟩ := G.boundary_isPair he
  refine ⟨e, he, hKe, ?_⟩
  have hxB : x ∈ G.edgeBoundary e :=
    ⟨G.edge_eq_inter_closure_edgeInterior he ▸ ⟨G.subset hx, closure_mono hKe hxK⟩, hx⟩
  have hyB : y ∈ G.edgeBoundary e :=
    ⟨G.edge_eq_inter_closure_edgeInterior he ▸ ⟨G.subset hy, closure_mono hKe hyK⟩, hy⟩
  obtain hx | hx := hb ▸ hxB <;> obtain hy | hy := hb ▸ hyB <;> simp_all [pair_comm]

/-- Every edge of a refinement lies in a unique original edge. -/
lemma finer.existsUnique_edge (hGH : G.finer H) (he : e ∈ E(H)) :
    ∃! f : Set X, f ∈ E(G) ∧ H.edgeInterior e ⊆ G.edgeInterior f ∧ e ⊆ f := by
  have h : H.edgeInterior e ⊆ G.carrier \ V(G) := by
    grw [hGH.carrier_eq, hGH.vertices_subset]
    exact H.edgeInterior_subset he
  obtain ⟨f, hf, hef⟩ := G.exists_edge_of_isConnected (H.edgeInterior_isConnected he) h
  refine ⟨f, ⟨hf, hef, ?_⟩, ?_⟩
  · intro z hz
    rw [← G.edge_eq_inter_closure_edgeInterior hf]
    exact ⟨hGH.carrier_eq.symm ▸ H.edge_subset he hz,
      closure_mono hef (H.edge_subset_closure_edgeInterior he hz)⟩
  rintro g ⟨hg, heg, _⟩
  obtain ⟨x, hx⟩ := H.edgeInterior_nonempty he
  exact G.edge_eq_of_mem_edgeInterior hg hf (heg hx) (hef hx)

namespace IsLink

variable {G}

lemma edge_mem (h : G.IsLink e x y) : e ∈ E(G) := h.1
lemma boundary_eq (h : G.IsLink e x y) : G.edgeBoundary e = {x, y} := h.2
lemma left_mem (h : G.IsLink e x y) : x ∈ V(G) :=
  (G.edgeBoundary_subset_vertexSet e) (h.2.symm ▸ mem_insert x {y})
lemma right_mem (h : G.IsLink e x y) : y ∈ V(G) :=
  (G.edgeBoundary_subset_vertexSet e) (h.2.symm ▸ mem_insert_of_mem _ (mem_singleton y))
lemma isPrimitiveLink (h : G.IsLink e x y) : IsPrimitiveLink e x y :=
  G.edge_isPrimitiveLink h.1 h.2
@[symm] lemma symm (h : G.IsLink e x y) : G.IsLink e y x := ⟨h.1, h.2.trans (pair_comm _ _)⟩

end IsLink

end GraphLike
