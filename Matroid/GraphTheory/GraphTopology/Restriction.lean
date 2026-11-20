module

public import Matroid.GraphTheory.GraphTopology.Assembly

@[expose] public section

open Set Topology Set.Notation

namespace GraphLike

variable {X : Type*} [TopologicalSpace X] (G : GraphLike X) (A : Set X) {C U W e : Set X} {x y : X}

private lemma restrict_decomposition :
    IsLinkDecomposition ((A ∩ V(G)) ∪ ⋃₀ {e ∈ E(G) | e ⊆ A})
      (A ∩ V(G)) {e ∈ E(G) | e ⊆ A} := by
  let S := (A ∩ V(G)) ∪ ⋃₀ {e ∈ E(G) | e ⊆ A}
  have hSG : S ⊆ G := union_subset (inter_subset_right.trans G.subset)
    (sUnion_subset fun e he ↦ G.edge_subset he.1)
  have hSA : S ⊆ A := union_subset inter_subset_left (sUnion_subset fun _ he ↦ he.2)
  refine ⟨rfl, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨a, -, b, -, hb, hl⟩ := G.boundary_isPair he.1
    refine ⟨a, b, hl, ?_⟩
    rw [← hb, edgeBoundary]
    ext x
    simp only [mem_inter_iff]
    exact and_congr_right fun hx ↦ and_iff_right (he.2 hx)
  · let f := Set.inclusion hSG
    intro x hx y hy hxy
    obtain ⟨U, V, hU, hV, hxU, hyV, hcover, hd⟩ :=
      G.isTotallySeparated (x := f x) (y := f y) hx.2 hy.2
        (fun h ↦ hxy (Set.inclusion_injective hSG h))
    exact ⟨f ⁻¹' U, f ⁻¹' V, hU.preimage (continuous_inclusion _),
      hV.preimage (continuous_inclusion _), hxU, hyV, fun z hz ↦ hcover hz.2, hd.preimage f⟩
  · intro e he
    convert (G.interior_isOpen he.1).preimage (continuous_inclusion hSG) using 1
    ext x
    simp only [mem_preimage, mem_sdiff, mem_inter_iff, edgeInterior, Set.inclusion]
    exact and_congr_right fun _ ↦ not_congr (and_iff_right (hSA x.2))

/-- Restrict to the vertices and whole edges contained in `A`. -/
def restrict : GraphLike X :=
  haveI : T2Space ↥((A ∩ V(G)) ∪ ⋃₀ {e ∈ E(G) | e ⊆ A}) :=
    (IsEmbedding.inclusion
      (show (A ∩ V(G)) ∪ ⋃₀ {e ∈ E(G) | e ⊆ A} ⊆ (G : Set X) from
        union_subset (inter_subset_right.trans G.subset)
        (sUnion_subset fun e he ↦ G.edge_subset he.1))).t2Space
  (by exact restrict_decomposition G A :
    IsLinkDecomposition ((A ∩ V(G)) ∪ ⋃₀ {e ∈ E(G) | e ⊆ A})
      (A ∩ V(G)) {e ∈ E(G) | e ⊆ A}).toGraphLike

lemma coe_restrict : (G.restrict A : Set X) = (A ∩ V(G)) ∪ ⋃₀ {e ∈ E(G) | e ⊆ A} := rfl

@[simp, grind =] lemma restrict_vertexSet : V(G.restrict A) = A ∩ V(G) := rfl

lemma restrict_subset : (G.restrict A : Set X) ⊆ A := by
  rintro x (hx | hx)
  · exact hx.1
  obtain ⟨e, ⟨_, heA⟩, hx⟩ := mem_sUnion.mp hx
  exact heA hx

lemma restrict_subset_self : (G.restrict A : Set X) ⊆ G := by
  rintro x (hx | hx)
  · exact G.subset hx.2
  obtain ⟨e, ⟨he, _⟩, hx⟩ := mem_sUnion.mp hx
  exact G.edge_subset he hx

lemma restrict_mono (hAC : A ⊆ C) : (G.restrict A : Set X) ⊆ G.restrict C := by
  rintro x (hx | hx)
  · exact Or.inl ⟨hAC hx.1, hx.2⟩
  obtain ⟨e, ⟨he, heA⟩, hx⟩ := mem_sUnion.mp hx
  exact Or.inr (mem_sUnion.mpr ⟨e, ⟨he, heA.trans hAC⟩, hx⟩)

lemma edge_subset_restrict {G A} (he : e ∈ E(G)) (heA : e ⊆ A) : e ⊆ G.restrict A :=
  fun _ hx ↦ Or.inr (mem_sUnion.mpr ⟨e, ⟨he, heA⟩, hx⟩)

@[simp] lemma restrict_edgeSet : E(G.restrict A) = {e ∈ E(G) | e ⊆ A} := by
  exact edgeSet_eq (restrict_decomposition G A)

lemma restrict_maximal {H : GraphLike X} (hV : V(H) ⊆ V(G)) (hE : E(H) ⊆ E(G))
    (hA : (H : Set X) ⊆ A) : (H : Set X) ⊆ G.restrict A := by
  rw [H.carrier_eq_vertexSet_union_sUnion_edges]
  rintro x (hx | hx)
  · exact Or.inl ⟨hA (H.subset hx), hV hx⟩
  obtain ⟨e, he, hx⟩ := mem_sUnion.mp hx
  exact G.edge_subset_restrict (hE he) ((H.edge_subset he).trans hA) hx

@[simp] lemma restrict_inter_vertexSet : (G.restrict A : Set X) ∩ V(G) = A ∩ V(G) :=
  subset_antisymm (inter_subset_inter_left _ (G.restrict_subset A))
    (fun _ hx ↦ ⟨Or.inl hx, hx.2⟩)

lemma interior_inter_restrict {G} (he : e ∈ E(G)) :
    G.edgeInterior e ∩ G.restrict A = {x ∈ G.edgeInterior e | e ⊆ A} := by
  ext x
  refine ⟨fun ⟨hx, hy⟩ ↦ ?_, fun ⟨hx, heA⟩ ↦ ⟨hx, G.edge_subset_restrict he heA hx.1⟩⟩
  rcases hy with hy | hy
  · exact False.elim (hx.2 hy.2)
  obtain ⟨f, ⟨hf, hfA⟩, hxf⟩ := mem_sUnion.mp hy
  obtain rfl := G.edge_eq_of_mem_edgeInterior he hf hx ⟨hxf, hx.2⟩
  exact ⟨hx, hfA⟩

lemma edge_subset_restrict_iff {G} (he : e ∈ E(G)) : e ⊆ G.restrict A ↔ e ⊆ A :=
  ⟨fun h ↦ h.trans (G.restrict_subset A), G.edge_subset_restrict he⟩

@[simp] lemma restrict_edgeInterior {A} (heA : e ⊆ A) :
    (G.restrict A).edgeInterior e = G.edgeInterior e := by
  ext x
  change (x ∈ e ∧ ¬ (x ∈ A ∧ x ∈ V(G))) ↔ x ∈ e ∧ x ∉ V(G)
  grind

@[simp] lemma restrict_edgeBoundary {A} (heA : e ⊆ A) :
    (G.restrict A).edgeBoundary e = G.edgeBoundary e := by
  ext x
  change (x ∈ e ∧ x ∈ A ∧ x ∈ V(G)) ↔ x ∈ e ∧ x ∈ V(G)
  grind

lemma restrict_eq_iff : G.restrict A = G.restrict C ↔ (G.restrict A : Set X) = G.restrict C := by
  refine ⟨fun h ↦ congrArg GraphLike.carrier h, fun h ↦ GraphLike.ext h ?_⟩
  change A ∩ V(G) = C ∩ V(G)
  rw [← G.restrict_inter_vertexSet A, ← G.restrict_inter_vertexSet C, h]

lemma restrict_finite_iff : (G.restrict A).Finite ↔ (A ∩ V(G)).Finite ∧ {e ∈ E(G) | e ⊆ A}.Finite :=
  ⟨fun h ↦ ⟨h.vertexSet_finite, by simpa only [restrict_edgeSet] using h.edgeSet_finite⟩,
    fun ⟨hV, hE⟩ ↦ ⟨hV, by simpa only [restrict_edgeSet] using hE⟩⟩

instance restrict_finite [G.Finite] : (G.restrict A).Finite :=
  (G.restrict_finite_iff A).mpr
    ⟨Finite.vertexSet_finite.subset inter_subset_right,
    Finite.edgeSet_finite.subset (sep_subset _ _)⟩

@[simp] lemma coe_restrict_empty : (G.restrict ∅ : Set X) = ∅ :=
  subset_antisymm (G.restrict_subset ∅) (empty_subset _)

@[simp] lemma restrict_univ : G.restrict univ = G := by
  refine GraphLike.ext ?_ (by simp)
  simpa only [coe_restrict, subset_univ, inf_of_le_right, and_true, ofPred_mem_eq] using
    G.carrier_eq_vertexSet_union_sUnion_edges.symm

@[simp] lemma restrict_self : G.restrict G = G :=
  GraphLike.ext (subset_antisymm (G.restrict_subset G)
    (G.restrict_maximal G Subset.rfl Subset.rfl Subset.rfl)) (inter_eq_right.mpr G.subset)

@[simp] lemma restrict_coe_restrict : G.restrict (G.restrict A) = G.restrict A := by
  apply (G.restrict_eq_iff _).mpr
  refine subset_antisymm (G.restrict_subset _) ?_
  rintro x (hx | hx)
  · exact Or.inl ⟨Or.inl hx, hx.2⟩
  obtain ⟨e, ⟨he, heA⟩, hx⟩ := mem_sUnion.mp hx
  exact G.edge_subset_restrict he (G.edge_subset_restrict he heA) hx

-- A union can complete an edge which neither input contains on its own.
lemma restrict_union_subset (C : Set X) :
    (G.restrict A : Set X) ∪ G.restrict C ⊆ G.restrict (A ∪ C) :=
  union_subset (G.restrict_mono A subset_union_left) (G.restrict_mono C subset_union_right)

lemma coe_restrict_union_restrict (C : Set X) :
    (G.restrict ((G.restrict A : Set X) ∪ G.restrict C) : Set X) =
      (G.restrict A : Set X) ∪ G.restrict C := by
  refine subset_antisymm (G.restrict_subset _) ?_
  simpa only [restrict_coe_restrict] using G.restrict_union_subset (G.restrict A) (G.restrict C)

lemma coe_restrict_inter (C : Set X) :
    (G.restrict (A ∩ C) : Set X) = (G.restrict A : Set X) ∩ G.restrict C := by
  refine subset_antisymm (subset_inter (G.restrict_mono _ inter_subset_left)
    (G.restrict_mono _ inter_subset_right)) fun x ⟨hxA, hxC⟩ ↦ ?_
  by_cases hxV : x ∈ V(G)
  · exact Or.inl ⟨⟨G.restrict_subset A hxA, G.restrict_subset C hxC⟩, hxV⟩
  obtain ⟨e, he, hxe⟩ := G.exists_edge_of_mem ⟨G.restrict_subset_self A hxA, hxV⟩
  have heA := ((G.interior_inter_restrict A he).subset ⟨hxe, hxA⟩).2
  have heC := ((G.interior_inter_restrict C he).subset ⟨hxe, hxC⟩).2
  exact G.edge_subset_restrict he (subset_inter heA heC) hxe.1

@[simp] lemma restrict_inter_self : G.restrict (A ∩ G) = G.restrict A := by
  rw [(G.restrict_eq_iff _), G.coe_restrict_inter A G, G.restrict_self]
  exact inter_eq_left.mpr (G.restrict_subset_self A)

lemma restrict_restrict (C : Set X) : (G.restrict A).restrict C = G.restrict (A ∩ C) := by
  refine GraphLike.ext ?_ ?_
  · simp only [coe_restrict, restrict_vertexSet, restrict_edgeSet, mem_ofPred_eq, and_assoc,
      subset_inter_iff]
    grind
  ext x
  grind [restrict_vertexSet]

variable {G A}

-- Finiteness concerns the retained vertices and edges, not the point set A.
lemma isCompact_restrict (hV : (A ∩ V(G)).Finite) (hE : {e ∈ E(G) | e ⊆ A}.Finite) :
    IsCompact ((G : Set X) ↓∩ (G.restrict A : Set X)) := by
  apply IsInducing.subtypeVal.isCompact_preimage'
  · exact hV.isCompact.union (hE.isCompact_sUnion fun e he ↦ G.edge_isCompact he.1)
  simpa only [Subtype.range_coe] using G.restrict_subset_self A

-- Closure restores endpoints of surviving edges, including endpoints in C.
lemma closure_restrict_sdiff (hV : (A ∩ V(G)).Finite) (hE : {e ∈ E(G) | e ⊆ A}.Finite) :
    (G : Set X) ∩ closure ((G.restrict A : Set X) \ G.restrict C) =
      ((A ∩ V(G)) \ C) ∪ ⋃₀ {e ∈ E(G) | e ⊆ A ∧ ¬ e ⊆ C} := by
  let S := ((A ∩ V(G)) \ C) ∪ ⋃₀ {e ∈ E(G) | e ⊆ A ∧ ¬ e ⊆ C}
  have hSG : S ⊆ G := union_subset
    (sdiff_subset.trans (inter_subset_right.trans G.subset))
    (sUnion_subset fun e he ↦ G.edge_subset he.1)
  have hE' : {e ∈ E(G) | e ⊆ A ∧ ¬ e ⊆ C}.Finite :=
    hE.subset fun _ he ↦ ⟨he.1, he.2.1⟩
  have hc : IsCompact S :=
    hV.sdiff.isCompact.union (hE'.isCompact_sUnion fun e he ↦ G.edge_isCompact he.1)
  have hclosed : IsClosed ((G : Set X) ↓∩ S) :=
    (IsInducing.subtypeVal.isCompact_preimage' hc
      (by simpa only [Subtype.range_coe] using hSG)).isClosed
  have hsub : (G.restrict A : Set X) \ G.restrict C ⊆ S := by
    rintro x ⟨hx | hx, hn⟩
    · exact Or.inl ⟨hx, fun hxC ↦ hn (Or.inl ⟨hxC, hx.2⟩)⟩
    obtain ⟨e, ⟨he, heA⟩, hx⟩ := mem_sUnion.mp hx
    exact Or.inr (mem_sUnion.mpr
      ⟨e, ⟨he, heA, fun heC ↦ hn (G.edge_subset_restrict he heC hx)⟩, hx⟩)
  change (G : Set X) ∩ closure ((G.restrict A : Set X) \ G.restrict C) = S
  apply subset_antisymm
  · rintro x ⟨hxG, hx⟩
    have hx' : (⟨x, hxG⟩ : G) ∈ closure
        ((G : Set X) ↓∩ ((G.restrict A : Set X) \ G.restrict C)) := by
      rw [closure_subtype]
      simpa only [image_preimage_eq_inter_range, Subtype.range_coe,
        inter_eq_left.mpr (sdiff_subset.trans (G.restrict_subset_self A))] using hx
    exact hclosed.closure_subset (closure_mono (preimage_mono hsub) hx')
  rintro x (hv | hx)
  · exact ⟨G.subset hv.1.2, subset_closure ⟨Or.inl hv.1, fun hxC ↦ hv.2 (G.restrict_subset C hxC)⟩⟩
  obtain ⟨e, ⟨he, heA, heC⟩, hx⟩ := mem_sUnion.mp hx
  refine ⟨G.edge_subset he hx, closure_mono (s := G.edgeInterior e) ?_
    (G.edge_subset_closure_edgeInterior he hx)⟩
  refine fun y hy ↦ ⟨G.edge_subset_restrict he heA hy.1, fun hyC ↦ ?_⟩
  exact heC (((G.interior_inter_restrict C he).subset ⟨hy, hyC⟩).2)

lemma coe_restrict_relativeClosure_sdiff (C : Set X) (hV : (A ∩ V(G)).Finite)
    (hE : {e ∈ E(G) | e ⊆ A}.Finite) :
    (G.restrict ((G : Set X) ∩ closure ((G.restrict A : Set X) \ G.restrict C)) : Set X) =
      (G : Set X) ∩ closure ((G.restrict A : Set X) \ G.restrict C) := by
  rw [G.closure_restrict_sdiff hV hE]
  refine subset_antisymm (G.restrict_subset _) ?_
  rintro x (hx | hx)
  · exact Or.inl ⟨Or.inl hx, hx.1.2⟩
  obtain ⟨e, he, hx⟩ := mem_sUnion.mp hx
  exact G.edge_subset_restrict he.1 (fun _ hy ↦ Or.inr (mem_sUnion.mpr ⟨e, he, hy⟩)) hx

lemma restrict_relativeClosure_sdiff_finite (C : Set X) (hV : (A ∩ V(G)).Finite)
    (hE : {e ∈ E(G) | e ⊆ A}.Finite) :
    (G.restrict ((G : Set X) ∩ closure ((G.restrict A : Set X) \ G.restrict C))).Finite := by
  have hsub : (G : Set X) ∩ closure ((G.restrict A : Set X) \ G.restrict C) ⊆ A := by
    rw [G.closure_restrict_sdiff hV hE]
    rintro x (hx | hx)
    · exact hx.1.1
    obtain ⟨e, he, hx⟩ := mem_sUnion.mp hx
    exact he.2.1 hx
  rw [G.restrict_finite_iff]
  exact ⟨hV.subset (inter_subset_inter_left _ hsub), hE.subset (fun _ he ↦ ⟨he.1, he.2.trans hsub⟩)⟩

/-! ## Vertex induction -/

variable (G)

private lemma induce_decomposition (U : Set X) :
    IsLinkDecomposition ((V(G) ∩ U) ∪ ⋃₀ {e ∈ E(G) | G.edgeBoundary e ⊆ U})
      (V(G) ∩ U) {e ∈ E(G) | G.edgeBoundary e ⊆ U} := by
  let S := (V(G) ∩ U) ∪ ⋃₀ {e ∈ E(G) | G.edgeBoundary e ⊆ U}
  have hvertex {x : X} (hx : x ∈ V(G)) : x ∈ S ↔ x ∈ U := by
    refine ⟨?_, fun hxU ↦ Or.inl ⟨hx, hxU⟩⟩
    rintro (hxU | hxU)
    · exact hxU.2
    obtain ⟨e, he, hxe⟩ := mem_sUnion.mp hxU
    exact he.2 ⟨hxe, hx⟩
  have hV : S ∩ V(G) = V(G) ∩ U := by
    ext x
    exact ⟨fun h ↦ ⟨h.2, (hvertex h.2).mp h.1⟩,
      fun h ↦ ⟨(hvertex h.1).mpr h.2, h.1⟩⟩
  have hE : {e ∈ E(G) | e ⊆ S} = {e ∈ E(G) | G.edgeBoundary e ⊆ U} := by
    ext e
    refine and_congr_right fun he ↦ ⟨?_, ?_⟩
    · exact fun h x hx ↦ (hvertex hx.2).mp (h hx.1)
    · exact fun h x hx ↦ Or.inr (mem_sUnion.mpr ⟨e, ⟨he, h⟩, hx⟩)
  simpa only [hV, hE] using restrict_decomposition G S

/-- The graph induced by the vertices in `U`, retaining every edge whose endpoints
belong to `U`. The ambient points outside `V(G)` do not affect the selection. -/
def induce (U : Set X) : GraphLike X :=
  haveI : T2Space ↥((V(G) ∩ U) ∪ ⋃₀ {e ∈ E(G) | G.edgeBoundary e ⊆ U}) :=
    (IsEmbedding.inclusion
      (show (V(G) ∩ U) ∪ ⋃₀ {e ∈ E(G) | G.edgeBoundary e ⊆ U} ⊆ (G : Set X) from
        union_subset (inter_subset_left.trans G.subset)
          (sUnion_subset fun _ he ↦ G.edge_subset he.1))).t2Space
  (by exact induce_decomposition G U :
    IsLinkDecomposition ((V(G) ∩ U) ∪ ⋃₀ {e ∈ E(G) | G.edgeBoundary e ⊆ U})
      (V(G) ∩ U) {e ∈ E(G) | G.edgeBoundary e ⊆ U}).toGraphLike

lemma coe_induce (U : Set X) :
    (G.induce U : Set X) = (V(G) ∩ U) ∪ ⋃₀ {e ∈ E(G) | G.edgeBoundary e ⊆ U} := rfl

@[simp] lemma induce_vertexSet (U : Set X) : V(G.induce U) = V(G) ∩ U := rfl

@[simp] lemma induce_edgeSet (U : Set X) : E(G.induce U) = {e ∈ E(G) | G.edgeBoundary e ⊆ U} :=
  edgeSet_eq (induce_decomposition G U)

lemma induce_subset (U : Set X) : (G.induce U : Set X) ⊆ G :=
  union_subset (inter_subset_left.trans G.subset) (sUnion_subset fun _ he ↦ G.edge_subset he.1)

variable {G}

@[simp, grind =]
lemma mem_induce_of_mem_vertexSet (hx : x ∈ V(G)) : x ∈ G.induce U ↔ x ∈ U := by
  refine ⟨?_, fun hxU ↦ Or.inl ⟨hx, hxU⟩⟩
  rintro (hxU | hxU)
  · exact hxU.2
  obtain ⟨e, he, hxe⟩ := mem_sUnion.mp hxU
  exact he.2 ⟨hxe, hx⟩

lemma mem_induce_of_mem_edgeInterior (he : e ∈ E(G)) (hx : x ∈ G.edgeInterior e) :
    x ∈ G.induce U ↔ G.edgeBoundary e ⊆ U := by
  refine ⟨?_, fun heU ↦ Or.inr (mem_sUnion.mpr ⟨e, ⟨he, heU⟩, hx.1⟩)⟩
  rintro (hxU | hxU)
  · exact (hx.2 hxU.1).elim
  obtain ⟨f, hf, hxf⟩ := mem_sUnion.mp hxU
  obtain rfl := G.edge_eq_of_mem_edgeInterior he hf.1 hx ⟨hxf, hx.2⟩
  exact hf.2

lemma edge_subset_induce_iff (he : e ∈ E(G)) : e ⊆ G.induce U ↔ G.edgeBoundary e ⊆ U :=
  ⟨fun h _ hx ↦ (G.mem_induce_of_mem_vertexSet hx.2).mp (h hx.1),
    fun h _ hx ↦ Or.inr (mem_sUnion.mpr ⟨e, ⟨he, h⟩, hx⟩)⟩

lemma edge_inter_induce (he : e ∈ E(G)) (hU : ¬ G.edgeBoundary e ⊆ U) :
    e ∩ G.induce U = G.edgeBoundary e ∩ U := by
  ext x
  refine ⟨fun ⟨hxe, hxU⟩ ↦ ?_,
    fun ⟨hxB, hxU⟩ ↦ ⟨hxB.1, (G.mem_induce_of_mem_vertexSet hxB.2).mpr hxU⟩⟩
  by_cases hxV : x ∈ V(G)
  · exact ⟨⟨hxe, hxV⟩, (G.mem_induce_of_mem_vertexSet hxV).mp hxU⟩
  exact (hU ((G.mem_induce_of_mem_edgeInterior he ⟨hxe, hxV⟩).mp hxU)).elim

lemma IsLink.inter_induce (hxy : G.IsLink e x y) (hx : x ∈ U) (hy : y ∉ U) :
    e ∩ G.induce U = {x} := by
  rw [G.edge_inter_induce hxy.edge_mem (fun h ↦ hy (h (by simp [hxy.boundary_eq]))),
    hxy.boundary_eq]
  ext z
  simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff]
  grind

lemma induce_congr (h : ∀ x ∈ V(G), x ∈ U ↔ x ∈ W) : G.induce U = G.induce W := by
  have hV : V(G) ∩ U = V(G) ∩ W := by
    ext x
    exact and_congr_right (h x)
  have hboundary (e : Set X) : G.edgeBoundary e ⊆ U ↔ G.edgeBoundary e ⊆ W :=
    ⟨fun he x hx ↦ (h x hx.2).mp (he hx), fun he x hx ↦ (h x hx.2).mpr (he hx)⟩
  refine GraphLike.ext ?_ hV
  simp only [coe_induce, hV, hboundary]

lemma induce_disjoint (hd : Disjoint (V(G) ∩ U) (V(G) ∩ W)) :
    Disjoint (G.induce U : Set X) (G.induce W : Set X) := by
  refine disjoint_left.mpr fun x hxU hxW ↦ ?_
  by_cases hxV : x ∈ V(G)
  · exact hd.notMem_of_mem_left ⟨hxV, (G.mem_induce_of_mem_vertexSet hxV).mp hxU⟩
      ⟨hxV, (G.mem_induce_of_mem_vertexSet hxV).mp hxW⟩
  obtain ⟨e, he, hxe⟩ := G.exists_edge_of_mem ⟨G.induce_subset U hxU, hxV⟩
  obtain ⟨a, ha, b, -, hab, -⟩ := G.boundary_isPair he
  have haB : a ∈ G.edgeBoundary e := by simp [hab]
  exact hd.notMem_of_mem_left ⟨ha, (G.mem_induce_of_mem_edgeInterior he hxe).mp hxU haB⟩
    ⟨ha, (G.mem_induce_of_mem_edgeInterior he hxe).mp hxW haB⟩

@[simp] lemma coe_induce_empty : (G.induce ∅ : Set X) = ∅ := by
  refine eq_empty_iff_forall_notMem.mpr ?_
  rintro x (hx | hx)
  · exact hx.2
  obtain ⟨e, he, -⟩ := mem_sUnion.mp hx
  obtain ⟨a, -, b, -, hab, -⟩ := G.boundary_isPair he.1
  exact he.2 (show a ∈ G.edgeBoundary e from by simp [hab])

@[simp] lemma induce_univ : G.induce univ = G := by
  refine GraphLike.ext ?_ (by simp)
  simpa only [coe_induce, subset_univ, inf_of_le_left, and_true, ofPred_mem_eq] using
    G.carrier_eq_vertexSet_union_sUnion_edges.symm

@[simp] lemma induce_inter_vertexSet (U : Set X) : (G.induce U : Set X) ∩ V(G) = V(G) ∩ U := by
  ext x
  exact ⟨fun h ↦ ⟨h.2, (G.mem_induce_of_mem_vertexSet h.2).mp h.1⟩,
    fun h ↦ ⟨(G.mem_induce_of_mem_vertexSet h.1).mpr h.2, h.1⟩⟩

@[simp] lemma restrict_induce (U : Set X) : G.restrict (G.induce U) = G.induce U := by
  refine GraphLike.ext ?_ (by rw [restrict_vertexSet, induce_vertexSet, induce_inter_vertexSet])
  refine (G.restrict_subset _).antisymm ?_
  rintro x (hx | hx)
  · exact Or.inl ⟨Or.inl hx, hx.1⟩
  obtain ⟨e, he, hxe⟩ := mem_sUnion.mp hx
  exact G.edge_subset_restrict he.1 ((G.edge_subset_induce_iff he.1).mpr he.2) hxe

@[simp] lemma induce_edgeBoundary (heU : G.edgeBoundary e ⊆ U) :
    (G.induce U).edgeBoundary e = G.edgeBoundary e := by
  ext x
  exact ⟨fun h ↦ ⟨h.1, h.2.1⟩, fun h ↦ ⟨h.1, h.2, heU h⟩⟩

@[simp] lemma induce_isLink : (G.induce U).IsLink e x y ↔ G.IsLink e x y ∧ x ∈ U ∧ y ∈ U := by
  refine ⟨fun ⟨he, hxy⟩ ↦ ?_, fun ⟨hxy, hx, hy⟩ ↦ ?_⟩
  · obtain ⟨he, heU⟩ := (G.induce_edgeSet U).subset he
    rw [G.induce_edgeBoundary heU] at hxy
    exact ⟨⟨he, hxy⟩, heU (by simp [hxy]), heU (by simp [hxy])⟩
  have heU : G.edgeBoundary e ⊆ U := by rw [hxy.boundary_eq]; exact pair_subset hx hy
  exact ⟨(G.induce_edgeSet U).superset ⟨hxy.edge_mem, heU⟩,
    (G.induce_edgeBoundary heU).trans hxy.boundary_eq⟩

@[simp] lemma induce_induce (U W : Set X) : (G.induce U).induce W = G.induce (U ∩ W) := by
  have hV : V((G.induce U).induce W) = V(G.induce (U ∩ W)) := by
    simp only [induce_vertexSet, inter_assoc]
  have hE : E((G.induce U).induce W) = E(G.induce (U ∩ W)) := by
    ext e
    simp only [induce_edgeSet, mem_ofPred_eq]
    refine ⟨fun ⟨⟨he, heU⟩, heW⟩ ↦ ?_, fun ⟨he, heUW⟩ ↦ ?_⟩
    · rw [G.induce_edgeBoundary heU] at heW
      exact ⟨he, subset_inter heU heW⟩
    have heU := heUW.trans inter_subset_left
    exact ⟨⟨he, heU⟩, G.induce_edgeBoundary heU ▸ heUW.trans inter_subset_right⟩
  refine GraphLike.ext ?_ hV
  rw [GraphLike.carrier_eq_vertexSet_union_sUnion_edges,
    GraphLike.carrier_eq_vertexSet_union_sUnion_edges, hV, hE]

/-- An open separation of the vertices in a compact carrier gives compact vertex-induced sides. -/
lemma isCompact_induce (hG : IsCompact G.carrier) (hU : IsOpen U) (hW : IsOpen W)
    (hd : Disjoint (↑G ∩ U) (G ∩ W)) (hc : V(G) ⊆ U ∪ W) : IsCompact (G.induce U : Set X) :=
  open Subtype in by
  let : CompactSpace G := isCompact_iff_compactSpace.mp hG
  let L := {e ∈ E(G) | G.edgeBoundary e ⊆ U}
  let F := {e | e ∈ E(G) ∧ ∃ x ∈ (show Set G from val ⁻¹' (U ∪ W)ᶜ), x.val ∈ e}
  suffices hKclosed : IsClosed (val ⁻¹' G.induce U : Set G) by
    have := hKclosed.isCompact.image continuous_subtypeVal
    rwa [image_preimage_eq_inter_range, range_coe, inter_eq_left.mpr <| G.induce_subset U] at this
  rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
  intro z hz
  obtain hzV | hzV := em' <| z.val ∈ V(G)
  · obtain ⟨e, he, hze⟩ := G.exists_edge_of_mem ⟨z.prop, hzV⟩
    exact ⟨val ⁻¹' G.edgeInterior e,
      fun y hy hyK ↦ hz <| (G.mem_induce_of_mem_edgeInterior he hze).mpr <|
      (G.mem_induce_of_mem_edgeInterior he hy).mp hyK, G.interior_isOpen he, hze⟩
  refine ⟨val ⁻¹' W \ val ⁻¹' ⋃₀ (F ∩ L), ?_, ?_,
    (hc hzV).resolve_left <| mt (G.mem_induce_of_mem_vertexSet hzV).mpr hz,
    (hz <| Or.inr <| sUnion_mono inter_subset_right ·)⟩
  · rintro y ⟨hyW, hyF⟩ (hyU | hyU)
    · exact hd.notMem_of_mem_left ⟨y.prop, hyU.right⟩ ⟨y.prop, hyW⟩
    obtain ⟨e, he, hye⟩ := mem_sUnion.mp hyU
    obtain ⟨a, -, b, -, hab, hl⟩ := G.boundary_isPair he.left
    obtain ⟨x, hxe, hx⟩ :=
      not_subset.mp <| (G.edge_isConnected he.left).isPreconnected.not_subset_union hU hW
        (hd.mono (inter_subset_inter_left _ <| G.edge_subset he.left) <| inter_subset_inter_left _
        <| G.edge_subset he.left) ⟨a, hl.left_mem, he.right (by simp [hab])⟩ ⟨y.val, hye, hyW⟩
    exact hyF <| mem_sUnion.mpr ⟨e, ⟨⟨he.left, ⟨x, G.edge_subset he.left hxe⟩, hx, hxe⟩, he⟩, hye⟩
  refine (hW.preimage continuous_subtypeVal).sdiff ?_
  refine (IsInducing.subtypeVal.isCompact_preimage' ?_ (by simpa only [range_coe] using
    (sUnion_subset fun e (he : e ∈ F ∩ L) ↦ G.edge_subset he.right.left))).isClosed
  exact ((G.finite_edges_meeting
    ((hU.union hW).isClosed_compl.preimage continuous_subtypeVal).isCompact
    fun x hx hv ↦ hx <| hc hv).inter_of_left _).isCompact_sUnion fun e he ↦ G.edge_isCompact
    he.right.left

end GraphLike
