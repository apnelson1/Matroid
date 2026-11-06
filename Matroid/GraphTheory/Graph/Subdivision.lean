module

public import Matroid.GraphTheory.Graph.TopologicalMinor

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

variable (M : J.TopologicalMinor G)

/-- A heterogeneous topological-minor witness is exhaustive when its branch vertices and route
interiors cover every host vertex and its routes cover every host edge. -/
def IsExhaustive : Prop :=
  V(G) ⊆ range M.branchVertex ∪ ⋃ e : E(J), (M.route e).internalVertexSet ∧
    E(G) ⊆ ⋃ e : E(J), E(M.route e)

lemma IsExhaustive.vertex_covers (h : M.IsExhaustive) :
    V(G) ⊆ range M.branchVertex ∪ ⋃ e : E(J), (M.route e).internalVertexSet := h.1

lemma IsExhaustive.edge_covers (h : M.IsExhaustive) :
    E(G) ⊆ ⋃ e : E(J), E(M.route e) := h.2

end TopologicalMinor

/-! ## Subdivision witness structures -/

/-- An isomorphism-invariant subdivision of `J` onto all of `G`. -/
structure Subdivision (J : Graph γ δ) (G : Graph α β) extends J.TopologicalMinor G where
  exhaustive : toTopologicalMinor.IsExhaustive

/-- The proposition that `G` is a subdivision of `J`, up to graph isomorphism of the pattern. -/
def IsSubdivision (J : Graph γ δ) (G : Graph α β) : Prop :=
  Nonempty (J.Subdivision G)

namespace Subdivision

variable (S : J.Subdivision G)

lemma vertex_covers : V(G) ⊆ range S.branchVertex ∪ ⋃ e : E(J), (S.route e).internalVertexSet :=
  S.exhaustive.vertex_covers

lemma edge_covers : E(G) ⊆ ⋃ e : E(J), E(S.route e) :=
  S.exhaustive.edge_covers

/-- A subdivision is, in particular, an isomorphism-invariant topological minor. -/
theorem toIsTopologicalMinor (S : J.Subdivision G) : J.IsTopologicalMinor G :=
  ⟨S.toTopologicalMinor⟩

/-- Enlarge the host of a subdivision.  Exhaustiveness is lost, so the result is a topological
minor rather than a subdivision. -/
noncomputable def mono_right {K : Graph α β} (hGK : G ≤ K) : J.TopologicalMinor K :=
  S.toTopologicalMinor.mono_right hGK

/-- Transport a subdivision along an isomorphism of its pattern. -/
noncomputable def ofIso {γ' δ' : Type*} {K : Graph γ' δ'} (F : Iso J K) (S : K.Subdivision G) :
    J.Subdivision G where
  toTopologicalMinor := TopologicalMinor.ofIso F S.toTopologicalMinor
  exhaustive := by
    refine ⟨fun x hx ↦ ?_, fun x hx ↦ ?_⟩
    · have hx' := S.vertex_covers hx
      simp only [mem_union, mem_iUnion, mem_range] at hx' ⊢
      obtain ⟨y, rfl⟩ | ⟨f, hf⟩ := hx'
      · obtain ⟨z, rfl⟩ := F.vertEquiv.surjective y
        exact Or.inl ⟨z, rfl⟩
      obtain ⟨e, rfl⟩ := F.edgeEquiv.surjective f
      exact Or.inr ⟨e, hf⟩
    have hx' := S.edge_covers hx
    simp only [mem_iUnion] at hx' ⊢
    obtain ⟨f, hf⟩ := hx'
    obtain ⟨e, rfl⟩ := F.edgeEquiv.surjective f
    exact ⟨e, hf⟩

end Subdivision

lemma IsSubdivision.isTopologicalMinor {J : Graph γ δ} {G : Graph α β}
    (h : J.IsSubdivision G) : J.IsTopologicalMinor G :=
  h.some.toIsTopologicalMinor

/-! ## Restricting a topological minor to its support -/

namespace TopologicalMinor

variable (M : J.TopologicalMinor G)

/-- A heterogeneous topological-minor witness is an exhaustive subdivision onto its used
subgraph. -/
noncomputable def subdivisionUsedSubgraph : J.Subdivision M.usedSubgraph where
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

end TopologicalMinor

/-! ## Characterizing topological minors by subdivisions of subgraphs -/

/-- A label-coherent topological minor is exactly a subdivision occurring as a subgraph of the
host. -/
theorem isTopologicalMinor_iff_exists_subdivision_subgraph {H G : Graph α β} :
    H.IsTopologicalMinor G ↔ ∃ K : Graph α β, K ≤ G ∧ H.IsSubdivision K :=
  ⟨fun ⟨M⟩ ↦ ⟨M.usedSubgraph, M.usedSubgraph_le, ⟨M.subdivisionUsedSubgraph⟩⟩,
    fun ⟨_, hKG, ⟨S⟩⟩ ↦ ⟨S.toTopologicalMinor.mono_right hKG⟩⟩

/-- An isomorphism-invariant topological minor is exactly an isomorphism-invariant subdivision
occurring as a subgraph of the host. -/
theorem isTopologicalMinor_iff_exists_Subdivision_subgraph {J : Graph γ δ} {G : Graph α β} :
    J.IsTopologicalMinor G ↔ ∃ K : Graph α β, K ≤ G ∧ J.IsSubdivision K :=
  ⟨fun ⟨M⟩ ↦ ⟨M.usedSubgraph, M.usedSubgraph_le, ⟨M.subdivisionUsedSubgraph⟩⟩,
    fun ⟨_, hKG, ⟨S⟩⟩ ↦ ⟨S.toTopologicalMinor.mono_right hKG⟩⟩

/-! ## Reflexivity -/

/-- Every graph is a subdivision of itself. -/
noncomputable def Subdivision.refl (G : Graph α β) : G.Subdivision G where
  toTopologicalMinor := TopologicalMinor.of_le le_rfl
  exhaustive := ⟨fun x hx ↦ Or.inl ⟨⟨x, hx⟩, rfl⟩,
    fun e he ↦ mem_iUnion.mpr ⟨⟨e, he⟩, by simp [TopologicalMinor.of_le]⟩⟩

@[simp]
lemma IsSubdivision.refl (G : Graph α β) : G.IsSubdivision G :=
  ⟨Subdivision.refl G⟩

end Graph
