module

public import Matroid.GraphTheory.GraphTopology.Defs
public import Matroid.MiniTauCeti.JCT.Topology.ConnectedComponent

/-! # Edges, faces, and finite carriers of graph-like spaces -/

@[expose] public section

open Set Function TopologicalSpace Topology Set.Notation

variable {X : Type*} [TopologicalSpace X] {K S e f : Set X} {G H : GraphLike X} {x y : X}

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

/-! ## Component sets

Edges are relative closures of the nonempty components of the vertex complement.
-/

@[simp] lemma componentClosure_mem_edgeSet (hx : x ∈ G.carrier \ V(G)) :
    G.carrier ∩ closure (connectedComponentIn (G.carrier \ V(G)) x) ∈ E(G) := ⟨x, hx, rfl⟩

@[simp] lemma edgeInterior_componentClosure (x : X) :
    G.edgeInterior (G.carrier ∩ closure (connectedComponentIn (G.carrier \ V(G)) x)) =
      connectedComponentIn (G.carrier \ V(G)) x := by
  convert (closure_connectedComponentIn_inter (U := G.carrier \ V(G)) (r := x)) using 1
  ext y
  simp only [edgeInterior, mem_sdiff, mem_inter_iff]
  tauto

@[simp] lemma edgeBoundary_componentClosure (x : X) :
    G.edgeBoundary (G.carrier ∩ closure (connectedComponentIn (G.carrier \ V(G)) x)) =
      (G.carrier ∩ closure (connectedComponentIn (G.carrier \ V(G)) x)) \
        connectedComponentIn (G.carrier \ V(G)) x := by
  refine (sdiff_sdiff_right_self _ _).symm.trans ?_
  congr
  nth_rw 2 [← edgeInterior_componentClosure]
  rfl

/-! ## Geometric edges -/

lemma edge_subset (he : e ∈ E(G)) : e ⊆ G.carrier := by
  obtain ⟨c, hc, rfl⟩ := he
  exact inter_subset_left

lemma edgeInterior_subset_edge (e : Set X) : G.edgeInterior e ⊆ e := sdiff_subset

lemma edgeBoundary_subset_edge (e : Set X) : G.edgeBoundary e ⊆ e := inter_subset_left

lemma edgeBoundary_subset_vertexSet (e : Set X) : G.edgeBoundary e ⊆ V(G) := inter_subset_right

lemma edgeInterior_subset (he : e ∈ E(G)) : G.edgeInterior e ⊆ G.carrier \ V(G) :=
  sdiff_subset_sdiff_left (G.edge_subset he)

lemma edgeInterior_nonempty (he : e ∈ E(G)) : (G.edgeInterior e).Nonempty := by
  obtain ⟨c, hc, rfl⟩ := he
  rw [edgeInterior_componentClosure]
  exact ⟨c, mem_connectedComponentIn hc⟩

/-- An interior point identifies the component set of its edge. -/
lemma edgeInterior_eq_connectedComponentIn (he : e ∈ E(G)) (hx : x ∈ G.edgeInterior e) :
    G.edgeInterior e = connectedComponentIn (G.carrier \ V(G)) x := by
  obtain ⟨p, hp, rfl⟩ := he
  rw [edgeInterior_componentClosure] at hx ⊢
  exact connectedComponentIn_eq hx

lemma edge_nonempty (he : e ∈ E(G)) : e.Nonempty :=
  (G.edgeInterior_nonempty he).mono (G.edgeInterior_subset_edge e)

lemma edgeInterior_isConnected (he : e ∈ E(G)) : IsConnected (G.edgeInterior e) := by
  obtain ⟨c, hc, rfl⟩ := he
  rw [edgeInterior_componentClosure]
  exact isConnected_connectedComponentIn_iff.mpr hc

lemma edgeInterior_eq_connectedComponentIn_of_subset (he : e ∈ E(G)) (heS : e ⊆ S) (hSG : S ⊆ G)
    (hx : x ∈ G.edgeInterior e) : G.edgeInterior e = connectedComponentIn (S \ V(G)) x := by
  refine subset_antisymm ((G.edgeInterior_isConnected he).isPreconnected.subset_connectedComponentIn
    hx (fun _ hy ↦ ⟨heS hy.1, hy.2⟩)) ?_
  rw [G.edgeInterior_eq_connectedComponentIn he hx]
  exact connectedComponentIn_mono _ (sdiff_subset_sdiff_left hSG)

lemma interior_isOpen (he : e ∈ E(G)) : IsOpen (G.carrier ↓∩ G.edgeInterior e) := by
  obtain ⟨c, hc, rfl⟩ := he
  simpa only [edgeInterior_componentClosure] using G.interior_isOpen' c hc

/-- Near an interior point of an edge, the whole carrier agrees with that edge. -/
lemma carrier_eventuallyEq_edge (he : e ∈ E(G)) (hx : x ∈ G.edgeInterior e) :
    G.carrier =ᶠ[𝓝 x] e := by
  obtain ⟨U, hU, hpre⟩ := Topology.IsInducing.subtypeVal.isOpen_iff.mp (G.interior_isOpen he)
  have hmem (y : G.carrier) : y.1 ∈ U ↔ y.1 ∈ G.edgeInterior e := by
    change y ∈ Subtype.val ⁻¹' U ↔ y ∈ Subtype.val ⁻¹' G.edgeInterior e
    rw [hpre]
  have hxU := (hmem ⟨x, G.edge_subset he hx.1⟩).mpr hx
  filter_upwards [hU.mem_nhds hxU] with y hy
  exact propext ⟨fun hyG ↦ ((hmem ⟨y, hyG⟩).mp hy).1, fun hy ↦ G.edge_subset he hy⟩

lemma boundary_isPair (he : e ∈ E(G)) :
    ∃ x ∈ V(G), ∃ y ∈ V(G), G.edgeBoundary e = {x, y} ∧ IsPrimitiveLink e x y := by
  obtain ⟨c, hc, rfl⟩ := he
  obtain ⟨x, y, hb, hl⟩ := G.boundary_isPair' c hc
  exact ⟨x, x.2, y, y.2, (G.edgeBoundary_componentClosure c).trans hb, hl⟩

/-- Every edge interior has an open unit-interval chart in the carrier.

This existence interface supplies a temporary chart for transporting closedness and
circuit-containment properties. Both circuit consumers discard the chart after that
transfer; neither returns a parametrization or requires the same chart in a later
operation. The statement therefore asserts availability without designating a chart. -/
lemma exists_isOpenEmbedding_edgeInterior (he : e ∈ E(G)) :
    ∃ f : Ioo (0 : unitInterval) 1 → G.carrier, IsOpenEmbedding f ∧
      range f = G.carrier ↓∩ G.edgeInterior e := by
  obtain ⟨a, ha, b, hb, hboundary, hlink⟩ := G.boundary_isPair he
  obtain ⟨P, hP, hPrange⟩ := hlink.restrictSubtype (G.edge_subset he)
  let f : Ioo (0 : unitInterval) 1 → G.carrier := fun t ↦ P t
  have hf : IsEmbedding f := IsEmbedding.subtypeVal.comp hP.isOpenEmbedding_interior.isEmbedding
  have hrange : range f = G.carrier ↓∩ G.edgeInterior e := by
    change range ((P : unitInterval → G.carrier) ∘ Subtype.val) = _
    rw [range_comp, Subtype.range_coe]
    change P.Interior = _
    rw [← hP.range_diff_endpoints, hPrange]
    ext z
    simp only [mem_sdiff, mem_preimage, mem_insert_iff, mem_singleton_iff, Subtype.ext_iff,
      edgeInterior]
    have hz : z.val ∈ e ∩ V(G) ↔ z.val = a ∨ z.val = b := by
      change z.val ∈ G.edgeBoundary e ↔ _
      rw [hboundary]
      rfl
    simp only [mem_inter_iff] at hz
    tauto
  exact ⟨f, ⟨hf, hrange.symm ▸ G.interior_isOpen he⟩, hrange⟩

lemma edge_isPrimitiveLink (he : e ∈ E(G)) (hb : G.edgeBoundary e = {x, y}) :
    IsPrimitiveLink e x y := by
  obtain ⟨a, _, b, _, hab, hlink⟩ := G.boundary_isPair he
  obtain ⟨ha, hb⟩ | ⟨ha, hb⟩ := pair_eq_pair_iff.mp (hab.symm.trans hb)
  · simpa only [ha, hb] using hlink
  simpa only [ha, hb] using hlink.symm

lemma edge_isCompact (he : e ∈ E(G)) : IsCompact e := by
  obtain ⟨x, _, y, _, _, h⟩ := G.boundary_isPair he
  exact h.isCompact

lemma edge_isConnected (he : e ∈ E(G)) : IsConnected e := by
  obtain ⟨_, _, _, _, _, h⟩ := G.boundary_isPair he
  exact h.isConnected

lemma edgeBoundary_finite (he : e ∈ E(G)) : (G.edgeBoundary e).Finite := by
  obtain ⟨x, _, y, _, hb, _⟩ := G.boundary_isPair he
  rw [hb]
  exact (finite_singleton _).insert _

lemma edgeInterior_disjoint (he : e ∈ E(G)) (hf : f ∈ E(G)) (hne : e ≠ f) :
    Disjoint (G.edgeInterior e) (G.edgeInterior f) := by
  obtain ⟨c, hc, rfl⟩ := he
  obtain ⟨d, hd, rfl⟩ := hf
  rw [edgeInterior_componentClosure, edgeInterior_componentClosure]
  exact disjoint_connectedComponentIn_of_ne (fun h ↦ hne (h ▸ rfl))

lemma edge_inter_subset_vertexSet (he : e ∈ E(G)) (hf : f ∈ E(G)) (hne : e ≠ f) :
    e ∩ f ⊆ V(G) := by
  rintro x ⟨hxe, hxf⟩
  by_contra hxV
  exact (G.edgeInterior_disjoint he hf hne).notMem_of_mem_left ⟨hxe, hxV⟩ ⟨hxf, hxV⟩

/-- A set of edges is recovered as the edges contained in its union. -/
lemma setOf_edge_subset_sUnion_eq {C : Set (Set X)} (hC : C ⊆ E(G)) :
    {e | e ∈ E(G) ∧ e ⊆ ⋃₀ C} = C := by
  apply subset_antisymm
  · rintro e ⟨he, hes⟩
    obtain ⟨x, hxe, hxV⟩ := G.edgeInterior_nonempty he
    obtain ⟨f, hf, hxf⟩ := mem_sUnion.mp (hes hxe)
    by_contra heC
    exact hxV (G.edge_inter_subset_vertexSet he (hC hf) (fun h ↦ heC (h ▸ hf)) ⟨hxe, hxf⟩)
  exact fun e he ↦ ⟨hC he, subset_sUnion_of_mem he⟩

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
  obtain ⟨c, hc, rfl⟩ := he
  rw [edgeInterior_componentClosure]

lemma edge_subset_closure_edgeInterior (he : e ∈ E(G)) : e ⊆ closure (G.edgeInterior e) :=
  fun _ hx ↦ ((G.edge_eq_inter_closure_edgeInterior he).symm ▸ hx).right

lemma edge_eq_inter_closure_edgeInterior_of_subset (he : e ∈ E(G)) {S : Set X}
    (heS : e ⊆ S) (hSG : S ⊆ G) : S ∩ closure (G.edgeInterior e) = e :=
  subset_antisymm
    ((inter_subset_inter_left _ hSG).trans (G.edge_eq_inter_closure_edgeInterior he).subset)
    (fun _ hx ↦ ⟨heS hx, G.edge_subset_closure_edgeInterior he hx⟩)

/-- Removing an edge interior leaves a relatively closed remainder of the carrier. -/
lemma edge_isClosed_remainder (he : e ∈ E(G)) :
    IsClosed (G.carrier ↓∩ (G.carrier \ G.edgeInterior e)) := by
  convert (G.interior_isOpen he).isClosed_compl using 1
  ext x
  simp only [mem_preimage, mem_sdiff, x.property, true_and, mem_compl_iff]

lemma edge_inter_remainder (he : e ∈ E(G)) :
    e ∩ (G.carrier \ G.edgeInterior e) = G.edgeBoundary e := by
  ext x
  simp only [edgeInterior, edgeBoundary, mem_inter_iff, mem_sdiff]
  grind [G.edge_subset he]

lemma edge_union_remainder (he : e ∈ E(G)) : e ∪ (G.carrier \ G.edgeInterior e) = G.carrier := by
  refine subset_antisymm (union_subset (G.edge_subset he) sdiff_subset) fun x hx ↦ ?_
  exact em (x ∈ G.edgeInterior e) |>.imp (G.edgeInterior_subset_edge e ·) (⟨hx, ·⟩)

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

lemma exists_edge_of_mem (hx : x ∈ G.carrier \ V(G)) : ∃ e ∈ E(G), x ∈ G.edgeInterior e := by
  refine ⟨_, G.componentClosure_mem_edgeSet hx, ?_⟩
  rw [edgeInterior_componentClosure]
  exact mem_connectedComponentIn hx

/-- A compact subset of the carrier avoiding the vertices meets finitely many edges. -/
lemma finite_edges_meeting {K : Set G} (hK : IsCompact K) (hV : ∀ x ∈ K, x.1 ∉ V(G)) :
    {e | e ∈ E(G) ∧ ∃ x ∈ K, x.1 ∈ e}.Finite := by
  classical
  obtain ⟨s, hs⟩ := hK.elim_finite_subcover
    (fun e : E(G) ↦ Subtype.val ⁻¹' G.edgeInterior e.1)
    (fun e ↦ G.interior_isOpen e.2) (by
      intro x hx
      obtain ⟨e, he, hxe⟩ := G.exists_edge_of_mem ⟨x.2, hV x hx⟩
      exact mem_iUnion.mpr ⟨⟨e, he⟩, hxe⟩)
  refine (s.finite_toSet.image Subtype.val).subset ?_
  rintro e ⟨he, x, hx, hxe⟩
  obtain ⟨f, hf, hxf⟩ := mem_iUnion₂.mp (hs hx)
  exact ⟨f, hf, (G.edge_eq_of_mem_edgeInterior he f.2 ⟨hxe, hV x hx⟩ hxf).symm⟩

lemma finite_edges_meeting_ambient {K : Set X} (hK : IsCompact K)
    (hKG : K ⊆ G.carrier) (hKV : Disjoint K V(G)) :
    {e ∈ E(G) | (e ∩ K).Nonempty}.Finite := by
  have hpre : IsCompact (Subtype.val ⁻¹' K : Set G) :=
    IsInducing.subtypeVal.isCompact_preimage' hK (by
      simpa only [Subtype.range_coe] using hKG)
  have hf := G.finite_edges_meeting hpre (fun x hx ↦ hKV.notMem_of_mem_left hx)
  refine hf.subset ?_
  rintro e ⟨he, x, hxe, hxK⟩
  exact ⟨he, ⟨x, hKG hxK⟩, hxK, hxe⟩

lemma carrier_eq_vertexSet_union_sUnion_edges : G.carrier = V(G) ∪ ⋃₀ E(G) := by
  refine Subset.antisymm (fun x hx ↦ ?_) ?_
  · rw [mem_union, or_iff_not_imp_left]
    intro hxV
    obtain ⟨e, he, hxe⟩ := G.exists_edge_of_mem ⟨hx, hxV⟩
    exact mem_sUnion.mpr ⟨e, he, G.edgeInterior_subset_edge e hxe⟩
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
  (G.isCompact_iff_vertexSet_isCompact Finite.edgeSet_finite).mpr Finite.vertexSet_finite.isCompact

lemma exists_edge_of_isConnected (hK : IsConnected K) (hsub : K ⊆ G.carrier \ V(G)) :
    ∃ e ∈ E(G), K ⊆ G.edgeInterior e := by
  obtain ⟨x, hx⟩ := hK.nonempty
  refine ⟨_, G.componentClosure_mem_edgeSet (hsub hx), ?_⟩
  rw [edgeInterior_componentClosure]
  exact hK.isPreconnected.subset_connectedComponentIn hx hsub

/-- A connected subset of the carrier avoiding vertices whose closure contains two distinct
vertices is an entire edge interior, with those vertices as its edge's boundary. -/
lemma exists_edge_of_isConnected_of_mem_closure (hK : IsConnected K) (hsub : K ⊆ G.carrier \ V(G))
    (hxy : x ≠ y) (hx : x ∈ V(G)) (hy : y ∈ V(G)) (hxK : x ∈ closure K) (hyK : y ∈ closure K) :
    ∃ e ∈ E(G), K = G.edgeInterior e ∧ G.edgeBoundary e = {x, y} := by
  obtain ⟨e, he, hKe⟩ := G.exists_edge_of_isConnected hK hsub
  have hb : G.edgeBoundary e = {x, y} := by
    obtain ⟨a, -, b, -, hb, -⟩ := G.boundary_isPair he
    have hxB : x ∈ G.edgeBoundary e :=
      ⟨G.edge_eq_inter_closure_edgeInterior he ▸ ⟨G.subset hx, closure_mono hKe hxK⟩, hx⟩
    have hyB : y ∈ G.edgeBoundary e :=
      ⟨G.edge_eq_inter_closure_edgeInterior he ▸ ⟨G.subset hy, closure_mono hKe hyK⟩, hy⟩
    clear hKe hxK hyK he hx hy hsub hK
    obtain rfl | rfl := hb ▸ hxB <;> obtain rfl | rfl := hb ▸ hyB <;> grind
  obtain ⟨γ, hinj, hrange⟩ :=
    (isPrimitiveLink_iff_exists_injective hxy).mp (G.edge_isPrimitiveLink he hb)
  have hconn : IsConnected (K ∪ {x, y}) :=
    hK.subset_closure subset_union_left (union_subset subset_closure (pair_subset hxK hyK))
  have hsubrange : K ∪ {x, y} ⊆ range γ := by
    rw [hrange, ← hb]
    exact union_subset (hKe.trans (G.edgeInterior_subset_edge e)) (G.edgeBoundary_subset_edge e)
  let : T2Space ↥(range γ) :=
    (IsEmbedding.inclusion (hrange ▸ G.edge_subset he)).t2Space
  have hfull := γ.image_Icc_subset_of_isConnected hinj hconn hsubrange
    (t₁ := 0) (t₂ := 1) (by simp) (by simp)
  rw [unitInterval.Icc_eq_univ, image_univ, hrange] at hfull
  refine ⟨e, he, hKe.antisymm ?_, hb⟩
  intro z hz
  obtain hzK | hzB := hfull hz.1
  · exact hzK
  exact False.elim (hz.2 ((pair_subset hx hy) hzB))

/-- Every edge of a refinement lies in a unique original edge. -/
lemma finer.existsUnique_edge (hGH : G.finer H) (he : e ∈ E(H)) :
    ∃! f : Set X, f ∈ E(G) ∧ H.edgeInterior e ⊆ G.edgeInterior f ∧ e ⊆ f := by
  have h : H.edgeInterior e ⊆ G.carrier \ V(G) := by
    grw [hGH.carrier_eq, hGH.vertices_subset]
    exact H.edgeInterior_subset he
  obtain ⟨f, hf, hef⟩ := G.exists_edge_of_isConnected (H.edgeInterior_isConnected he) h
  refine ⟨f, ⟨hf, hef, fun z hz ↦ ?_⟩, fun g ⟨hg, heg, _⟩ ↦ ?_⟩
  · rw [← G.edge_eq_inter_closure_edgeInterior hf]
    exact ⟨hGH.carrier_eq.symm ▸ H.edge_subset he hz,
      closure_mono hef (H.edge_subset_closure_edgeInterior he hz)⟩
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

lemma isPrimitiveLink (h : G.IsLink e x y) : IsPrimitiveLink e x y := G.edge_isPrimitiveLink h.1 h.2

@[symm] lemma symm (h : G.IsLink e x y) : G.IsLink e y x := ⟨h.1, h.2.trans (pair_comm _ _)⟩

end IsLink

variable {G} {F : Set X}

lemma subset_compl_of_mem_faceSet (hF : F ∈ F(G)) : F ⊆ G.carrierᶜ := by
  obtain ⟨x, _, rfl⟩ := hF
  exact connectedComponentIn_subset _ _

/-- The faces whose frontiers contain the given point. -/
def boundingFaces (G : GraphLike X) (x : X) : Set (Set X) :=
  {F | F ∈ F(G) ∧ x ∈ frontier F}

/-- Every face contains a point. -/
lemma nonempty_of_mem_faceSet (hF : F ∈ F(G)) : F.Nonempty := by
  obtain ⟨x, hx, rfl⟩ := hF
  exact ⟨x, mem_connectedComponentIn hx⟩

/-- A face is disjoint from the graphlike carrier. -/
lemma disjoint_carrier_of_mem_faceSet (hF : F ∈ F(G)) : Disjoint F G.carrier :=
  disjoint_left.mpr fun _ hx ↦ subset_compl_of_mem_faceSet hF hx

/-- A point of a face identifies its complementary connected component. -/
lemma eq_connectedComponentIn_of_mem_faceSet (hF : F ∈ F(G)) (hx : x ∈ F) :
    F = connectedComponentIn G.carrierᶜ x := by
  obtain ⟨y, _, rfl⟩ := hF
  exact connectedComponentIn_eq hx

/-- A face is connected. -/
lemma isConnected_of_mem_faceSet (hF : F ∈ F(G)) : IsConnected F := by
  obtain ⟨x, hx, rfl⟩ := hF
  exact isConnected_connectedComponentIn_iff.mpr hx

lemma mem_faceAt (hx : x ∉ G.carrier) : x ∈ G.faceAt x :=
  mem_connectedComponentIn hx

lemma mem_faceSet_of_mem_faceAt (hx : x ∉ G.carrier) : (G.faceAt x) ∈ F(G) := ⟨x, hx, rfl⟩

@[simp] lemma faceAt_eq_empty (hx : x ∈ G.carrier) : G.faceAt x = ∅ :=
  connectedComponentIn_eq_empty (not_not.mpr hx)

/-- Membership in a face is equality with the complementary component of the point. -/
@[simp] lemma mem_iff_of_mem_faceSet (hF : F ∈ F(G)) (hx : x ∉ G.carrier) :
    x ∈ F ↔ G.faceAt x = F := by
  refine ⟨fun hxF ↦ (eq_connectedComponentIn_of_mem_faceSet hF hxF).symm, ?_⟩
  rintro rfl
  exact mem_faceAt hx

/-- An open connected set disjoint from the carrier whose frontier lies in the carrier is a face. -/
lemma isFace_of_frontier_subset (hK : IsOpen K) (hc : IsConnected K)
    (hd : Disjoint K G.carrier) (hf : frontier K ⊆ G.carrier) : K ∈ F(G) := by
  obtain ⟨a, ha⟩ := hc.nonempty
  exact ⟨a, hd.notMem_of_mem_left ha,
    (eq_connectedComponentIn_of_frontier_subset hK hc.isPreconnected hd hf ha).symm⟩

/-- Faces of a closed carrier in a locally connected space are open. -/
lemma isOpen_of_mem_faceSet [LocallyConnectedSpace X] (hF : F ∈ F(G)) (hG : IsClosed G.carrier) :
    IsOpen F := by
  obtain ⟨x, _, rfl⟩ := hF
  exact hG.isOpen_compl.connectedComponentIn

/-- The frontier of a face of a closed carrier lies in the carrier. -/
lemma frontier_subset_carrier_of_mem_faceSet [LocallyConnectedSpace X] (hF : F ∈ F(G))
    (hG : IsClosed G.carrier) : frontier F ⊆ G.carrier := by
  obtain ⟨x, _, rfl⟩ := hF
  exact hG.frontier_connectedComponentIn_compl_subset

end GraphLike
