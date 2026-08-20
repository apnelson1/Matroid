module

public import Matroid.Graph.TopologicalMinor

/-!
# Graph subdivisions

A subdivision is an *exhaustive* topological-minor model: every host vertex and edge belongs to the
model.  This file is downstream of `Graph.TopologicalMinor`; users who only need topological-minor
containment do not need to import subdivision theory.

The central bridge is that every topological-minor witness becomes a subdivision after restricting
the host to its `usedSubgraph`.  Consequently,

`H` is a topological minor of `G` iff some subgraph of `G` is a subdivision of `H`.

Both label-coherent and isomorphism-invariant versions are developed in parallel.
-/

@[expose] public section

variable {α β γ δ : Type*} {G H K : Graph α β} {J L : Graph γ δ}

open Set WList Function
open scoped Sym2

namespace Graph

/-! ## Exhaustiveness predicates -/

namespace TopologicalMinor

variable (M : H.TopologicalMinor G)

/-- A label-coherent topological-minor witness is exhaustive when its branch vertices and route
interiors cover every host vertex and its routes cover every host edge. -/
def IsExhaustive : Prop :=
  V(G) ⊆ V(H) ∪ ⋃ e : E(H), (M.route e).internalVertexSet ∧ E(G) ⊆ ⋃ e : E(H), E(M.route e)

lemma IsExhaustive.vertex_covers (h : M.IsExhaustive) :
    V(G) ⊆ V(H) ∪ ⋃ e : E(H), (M.route e).internalVertexSet := h.1

lemma IsExhaustive.edge_covers (h : M.IsExhaustive) :
    E(G) ⊆ ⋃ e : E(H), E(M.route e) := h.2

end TopologicalMinor

namespace IsoTopologicalMinor

variable (M : J.IsoTopologicalMinor G)

/-- A heterogeneous topological-minor witness is exhaustive when its branch vertices and route
interiors cover every host vertex and its routes cover every host edge. -/
def IsExhaustive : Prop :=
  V(G) ⊆ range M.branchVertex ∪ ⋃ e : E(J), (M.route e).internalVertexSet ∧
    E(G) ⊆ ⋃ e : E(J), E(M.route e)

lemma IsExhaustive.vertex_covers (h : M.IsExhaustive) :
    V(G) ⊆ range M.branchVertex ∪ ⋃ e : E(J), (M.route e).internalVertexSet := h.1

lemma IsExhaustive.edge_covers (h : M.IsExhaustive) :
    E(G) ⊆ ⋃ e : E(J), E(M.route e) := h.2

end IsoTopologicalMinor

/-! ## Subdivision witness structures -/

/-- A label-coherent subdivision of `H` onto all of `G`. -/
structure Subdivision (H G : Graph α β) extends H.TopologicalMinor G where
  exhaustive : toTopologicalMinor.IsExhaustive

/-- An isomorphism-invariant subdivision of `J` onto all of `G`. -/
structure IsoSubdivision (J : Graph γ δ) (G : Graph α β) extends J.IsoTopologicalMinor G where
  exhaustive : toIsoTopologicalMinor.IsExhaustive

/-- The proposition that `G` is a label-coherent subdivision of `H`. -/
def IsSubdivision (H G : Graph α β) : Prop :=
  Nonempty (H.Subdivision G)

/-- The proposition that `G` is a subdivision of `J`, up to graph isomorphism of the pattern. -/
def IsIsoSubdivision (J : Graph γ δ) (G : Graph α β) : Prop :=
  Nonempty (J.IsoSubdivision G)

namespace Subdivision

variable (S : H.Subdivision G)

lemma vertex_covers :
    V(G) ⊆ V(H) ∪ ⋃ e : E(H), (S.route e).internalVertexSet :=
  S.exhaustive.vertex_covers

lemma edge_covers : E(G) ⊆ ⋃ e : E(H), E(S.route e) :=
  S.exhaustive.edge_covers

/-- A subdivision is, in particular, a topological minor. -/
theorem toIsTopologicalMinor (S : H.Subdivision G) : H.IsTopologicalMinor G :=
  ⟨S.toTopologicalMinor⟩

/-- Enlarge the host of a subdivision. Exhaustiveness is lost. -/
noncomputable def mono_right {K : Graph α β} (hGK : G ≤ K) : H.TopologicalMinor K :=
  S.toTopologicalMinor.mono_right hGK

/-- Regard a label-coherent subdivision as an isomorphism-invariant subdivision. -/
noncomputable def toIsoSubdivision : H.IsoSubdivision G where
  toIsoTopologicalMinor := S.toTopologicalMinor.toIsoTopologicalMinor
  exhaustive := by
    refine ⟨fun x hx ↦ ?_, S.edge_covers⟩
    have hx' := S.vertex_covers hx
    simp only [mem_union, mem_iUnion] at hx' ⊢
    obtain hxH | ⟨e, hxint⟩ := hx'
    · exact Or.inl ⟨⟨x, hxH⟩, rfl⟩
    exact Or.inr ⟨e, hxint⟩

end Subdivision

lemma IsSubdivision.isTopologicalMinor {H G : Graph α β} (h : H.IsSubdivision G) :
    H.IsTopologicalMinor G :=
  h.some.toIsTopologicalMinor

lemma IsSubdivision.isIsoSubdivision {H G : Graph α β} (h : H.IsSubdivision G) :
    H.IsIsoSubdivision G :=
  ⟨h.some.toIsoSubdivision⟩

namespace IsoSubdivision

variable (S : J.IsoSubdivision G)

lemma vertex_covers : V(G) ⊆ range S.branchVertex ∪ ⋃ e : E(J), (S.route e).internalVertexSet :=
  S.exhaustive.vertex_covers

lemma edge_covers : E(G) ⊆ ⋃ e : E(J), E(S.route e) :=
  S.exhaustive.edge_covers

/-- A subdivision is, in particular, an isomorphism-invariant topological minor. -/
theorem toIsIsoTopologicalMinor (S : J.IsoSubdivision G) : J.IsIsoTopologicalMinor G :=
  ⟨S.toIsoTopologicalMinor⟩

/-- Enlarge the host of a subdivision.  Exhaustiveness is lost, so the result is a topological
minor rather than a subdivision. -/
noncomputable def mono_right {K : Graph α β} (hGK : G ≤ K) : J.IsoTopologicalMinor K :=
  S.toIsoTopologicalMinor.mono_right hGK

/-- Transport a subdivision along an isomorphism of its pattern. -/
noncomputable def ofIso {γ' δ' : Type*} {K : Graph γ' δ'} (F : Iso J K) (S : K.IsoSubdivision G) :
    J.IsoSubdivision G where
  toIsoTopologicalMinor := IsoTopologicalMinor.ofIso F S.toIsoTopologicalMinor
  exhaustive := by
    refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
    · have hx' := S.vertex_covers hx
      simp only [mem_union, mem_iUnion, mem_range] at hx' ⊢
      obtain ⟨y, rfl⟩ | ⟨f, hf⟩ := hx'
      · obtain ⟨z, hz⟩ := F.vertMapEmbedding_surjective y
        exact Or.inl ⟨z, by simp [IsoTopologicalMinor.ofIso, hz]⟩
      obtain ⟨e, he⟩ := F.edgeMapEmbedding_surjective f
      exact Or.inr ⟨e, by simpa [IsoTopologicalMinor.ofIso, he] using hf⟩
    have hx' := S.edge_covers hx
    simp only [mem_iUnion] at hx' ⊢
    obtain ⟨f, hf⟩ := hx'
    obtain ⟨e, he⟩ := F.edgeMapEmbedding_surjective f
    exact ⟨e, by simpa [IsoTopologicalMinor.ofIso, he] using hf⟩

end IsoSubdivision

lemma IsIsoSubdivision.isIsoTopologicalMinor {J : Graph γ δ} {G : Graph α β}
    (h : J.IsIsoSubdivision G) : J.IsIsoTopologicalMinor G :=
  h.some.toIsIsoTopologicalMinor

/-! ## Restricting a topological minor to its support -/

namespace TopologicalMinor

variable (M : H.TopologicalMinor G)

/-- A topological-minor witness is an exhaustive subdivision onto its used subgraph. -/
noncomputable def subdivisionUsedSubgraph : H.Subdivision M.usedSubgraph where
  vertex_subset := by
    simp only [usedSubgraph, vertexSet_restrict, vertexSet_induce, usedVertexSet]
    exact subset_union_left
  route := M.route
  route_edge_mem := M.route_edge_mem
  route_isSimple := M.route_isSimple_usedSubgraph
  route_ends := M.route_ends
  route_internal_disjoint_branchVertices := M.route_internal_disjoint_branchVertices
  route_internal_disjoint := M.route_internal_disjoint
  exhaustive := by
    refine ⟨fun x hx ↦ ?_, fun f hf ↦ ?_⟩
    · simp only [usedSubgraph, vertexSet_restrict, vertexSet_induce, usedVertexSet, mem_union,
        mem_iUnion] at hx ⊢
      obtain hxH | ⟨e, hxroute⟩ := hx
      · exact Or.inl hxH
      obtain rfl | hi | rfl := mem_iff_eq_first_or_mem_internalVertexSet_or_eq_last.mp hxroute
      · exact Or.inl (M.route_isLink e).left_mem
      · exact Or.inr ⟨e, hi⟩
      · exact Or.inl (M.route_isLink e).right_mem
    simp only [usedSubgraph, edgeSet_restrict, mem_inter_iff, usedEdgeSet] at hf
    exact hf.2

/-- Exhaustiveness is equivalent to saying that the witness already uses the whole host. -/
theorem isExhaustive_iff_usedSubgraph_eq : M.IsExhaustive ↔ M.usedSubgraph = G := by
  have hused : M.usedVertexSet = V(H) ∪ ⋃ e : E(H), (M.route e).internalVertexSet := by
    ext x
    simp only [usedVertexSet, mem_union, mem_iUnion]
    refine ⟨fun h ↦ ?_, ?_⟩
    · obtain hxH | ⟨e, hxroute⟩ := h
      · exact Or.inl hxH
      obtain rfl | hi | rfl := mem_iff_eq_first_or_mem_internalVertexSet_or_eq_last.mp hxroute
      · exact Or.inl (M.route_isLink e).left_mem
      · exact Or.inr ⟨e, hi⟩
      exact Or.inl (M.route_isLink e).right_mem
    rintro (hxH | ⟨e, hi⟩)
    · exact Or.inl hxH
    exact Or.inr ⟨e, mem_iff_eq_first_or_mem_internalVertexSet_or_eq_last.mpr (Or.inr (Or.inl hi))⟩
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨?_, ?_⟩⟩
  · have hV : M.usedVertexSet = V(G) :=
      subset_antisymm M.usedVertexSet_subset (hused ▸ h.vertex_covers)
    rw [usedSubgraph, hV, induce_vertexSet, restrict_eq_self_iff]
    exact h.edge_covers
  · have hVeq : V(M.usedSubgraph) = M.usedVertexSet := by simp [usedSubgraph]
    rw [← hused, ← hVeq, h]
  have hE : E(M.usedSubgraph) ⊆ M.usedEdgeSet := by simp [usedSubgraph, edgeSet_restrict]
  rwa [h] at hE

end TopologicalMinor

namespace IsoTopologicalMinor

variable (M : J.IsoTopologicalMinor G)

/-- A heterogeneous topological-minor witness is an exhaustive subdivision onto its used
subgraph. -/
noncomputable def subdivisionUsedSubgraph : J.IsoSubdivision M.usedSubgraph where
  branchVertex := M.branchVertex
  branchVertex_mem x := by
    simp only [usedSubgraph, vertexSet_restrict, vertexSet_induce, usedVertexSet, mem_union]
    exact Or.inl ⟨x, rfl⟩
  route := M.route
  route_isSimple := M.route_isSimple_usedSubgraph
  route_nonempty := M.route_nonempty
  route_ends := M.route_ends
  route_internal_disjoint_branchVertices := M.route_internal_disjoint_branchVertices
  route_internal_disjoint := M.route_internal_disjoint
  route_edge_disjoint := M.route_edge_disjoint
  exhaustive := by
    refine ⟨fun x hx ↦ ?_, fun f hf ↦ ?_⟩
    · simp only [usedSubgraph, vertexSet_restrict, vertexSet_induce, usedVertexSet, mem_union,
        mem_iUnion, mem_range] at hx ⊢
      obtain hxbranch | ⟨e, hxroute⟩ := hx
      · exact Or.inl hxbranch
      obtain rfl | hi | rfl := mem_iff_eq_first_or_mem_internalVertexSet_or_eq_last.mp hxroute
      · exact Or.inl (M.ends_mem_range_branchVertex e).1
      · exact Or.inr ⟨e, hi⟩
      · exact Or.inl (M.ends_mem_range_branchVertex e).2
    simp only [usedSubgraph, edgeSet_restrict, mem_inter_iff, usedEdgeSet] at hf
    exact hf.2

/-- Exhaustiveness is equivalent to saying that the witness already uses the whole host. -/
theorem isExhaustive_iff_usedSubgraph_eq : M.IsExhaustive ↔ M.usedSubgraph = G := by
  have hused : M.usedVertexSet =
      range M.branchVertex ∪ ⋃ e : E(J), (M.route e).internalVertexSet := by
    ext x
    simp only [usedVertexSet, mem_union, mem_iUnion]
    constructor <;> rintro (hxbranch | ⟨e, hi⟩) <;> try { exact Or.inl hxbranch }
    · obtain rfl | hi | rfl := mem_iff_eq_first_or_mem_internalVertexSet_or_eq_last.mp hi
      · exact Or.inl (M.ends_mem_range_branchVertex e).1
      · exact Or.inr ⟨e, hi⟩
      exact Or.inl (M.ends_mem_range_branchVertex e).2
    exact Or.inr ⟨e, mem_iff_eq_first_or_mem_internalVertexSet_or_eq_last.mpr (Or.inr (Or.inl hi))⟩
  refine ⟨fun h ↦ ?_, fun h ↦ ⟨?_, ?_⟩⟩
  · have hV : M.usedVertexSet = V(G) :=
      subset_antisymm M.usedVertexSet_subset (hused ▸ h.vertex_covers)
    rw [usedSubgraph, hV, induce_vertexSet, restrict_eq_self_iff]
    exact h.edge_covers
  · rw [← hused, ← (show V(M.usedSubgraph) = M.usedVertexSet by simp [usedSubgraph]), h]
  have hE : E(M.usedSubgraph) ⊆ M.usedEdgeSet := by simp [usedSubgraph, edgeSet_restrict]
  rwa [h] at hE

end IsoTopologicalMinor

/-! ## Normalization of subdivisions -/

namespace IsoSubdivision

variable (S : J.IsoSubdivision G)

/-- Normalize an isomorphism-invariant subdivision to a label-coherent subdivision of an
isomorphic same-carrier copy of the pattern. -/
theorem exists_iso_subdivision (S : J.IsoSubdivision G) :
    ∃ K : Graph α β, Nonempty (Iso J K) ∧ Nonempty (K.Subdivision G) := by
  let M := S.toIsoTopologicalMinor
  refine ⟨M.normalized, ⟨M.isoNormalized⟩, ⟨M.toTopologicalMinor, ?_⟩⟩
  refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
  · have hx' := S.vertex_covers hx
    simp only [mem_union, mem_iUnion, mem_range, IsoTopologicalMinor.vertexSet_normalized]
      at hx' ⊢
    obtain ⟨y, rfl⟩ | ⟨e, he⟩ := hx'
    · exact Or.inl ⟨y, rfl⟩
    refine Or.inr ⟨⟨M.repEdge e, by simp [IsoTopologicalMinor.edgeSet_normalized]⟩, ?_⟩
    simpa [IsoTopologicalMinor.toTopologicalMinor, IsoTopologicalMinor.source_repEdge] using he
  have hx' := S.edge_covers hx
  simp only [mem_iUnion] at hx' ⊢
  obtain ⟨e, he⟩ := hx'
  refine ⟨⟨M.repEdge e, by simp [IsoTopologicalMinor.edgeSet_normalized]⟩, ?_⟩
  simpa [IsoTopologicalMinor.toTopologicalMinor, IsoTopologicalMinor.source_repEdge] using he

end IsoSubdivision

/-- The heterogeneous subdivision structure agrees with the label-coherent structure up to graph
isomorphism. -/
theorem isIsoSubdivision_iff_exists_iso_subdivision {J : Graph γ δ} {G : Graph α β} :
    J.IsIsoSubdivision G ↔ ∃ K : Graph α β, Nonempty (Iso J K) ∧ Nonempty (K.Subdivision G) :=
  ⟨fun ⟨S⟩ ↦ S.exists_iso_subdivision,
    fun ⟨_, ⟨F⟩, ⟨S⟩⟩ ↦ ⟨IsoSubdivision.ofIso F S.toIsoSubdivision⟩⟩

/-! ## Characterizing topological minors by subdivisions of subgraphs -/

/-- A label-coherent topological minor is exactly a subdivision occurring as a subgraph of the
host. -/
theorem isTopologicalMinor_iff_exists_subdivision_subgraph {H G : Graph α β} :
    H.IsTopologicalMinor G ↔ ∃ K : Graph α β, K ≤ G ∧ H.IsSubdivision K :=
  ⟨fun ⟨M⟩ ↦ ⟨M.usedSubgraph, M.usedSubgraph_le, ⟨M.subdivisionUsedSubgraph⟩⟩,
    fun ⟨_, hKG, ⟨S⟩⟩ ↦ ⟨S.toTopologicalMinor.mono_right hKG⟩⟩

/-- An isomorphism-invariant topological minor is exactly an isomorphism-invariant subdivision
occurring as a subgraph of the host. -/
theorem isIsoTopologicalMinor_iff_exists_isoSubdivision_subgraph {J : Graph γ δ} {G : Graph α β} :
    J.IsIsoTopologicalMinor G ↔ ∃ K : Graph α β, K ≤ G ∧ J.IsIsoSubdivision K :=
  ⟨fun ⟨M⟩ ↦ ⟨M.usedSubgraph, M.usedSubgraph_le, ⟨M.subdivisionUsedSubgraph⟩⟩,
    fun ⟨_, hKG, ⟨S⟩⟩ ↦ ⟨S.toIsoTopologicalMinor.mono_right hKG⟩⟩

/-! ## Reflexivity -/

/-- Every graph is a subdivision of itself. -/
noncomputable def Subdivision.refl (G : Graph α β) : G.Subdivision G where
  toTopologicalMinor := TopologicalMinor.of_le le_rfl
  exhaustive :=
    ⟨subset_union_left, fun e he ↦ mem_iUnion.mpr ⟨⟨e, he⟩, by simp [TopologicalMinor.of_le]⟩⟩

@[simp]
lemma IsSubdivision.refl (G : Graph α β) : G.IsSubdivision G :=
  ⟨Subdivision.refl G⟩

@[simp]
lemma IsIsoSubdivision.refl (G : Graph α β) : G.IsIsoSubdivision G :=
  ⟨(Subdivision.refl G).toIsoSubdivision⟩

end Graph
