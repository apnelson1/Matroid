module

public import Matroid.Graph.Planarity.Drawing
public import Matroid.Graph.Subgraph.Union

@[expose] public section

/-!
# Unions of graph drawings

This optional module glues drawings of two graphs whose edge sets are disjoint and whose images
meet only at consistently drawn shared vertices. Basic uses of `Drawing` do not import this file.

The construction is deliberately graph-generic. Path insertion is instead derived from edge
insertion and subdivision in `Matroid.Graph.Planarity.Insertion.Basic`.
-/

open Function Set Topology

namespace Graph.Drawing

noncomputable section

universe u

variable {α β : Type*} {G H : Graph α β} {X : Type u} [TopologicalSpace X]
  {D : Drawing G X} {D' : Drawing H X}

/-- Conditions under which two drawings glue to a drawing of the union graph. Shared vertices must
be placed at the same point, and the two supports may meet only at images of shared vertices. Edge
sets are required to be disjoint so no choice of an edge drawing is needed. -/
structure IsFreeUnion (D : Drawing G X) (D' : Drawing H X) : Prop where
  edgeSet_disjoint : Disjoint E(G) E(H)
  agree_vertex : ∀ (x : α) (hG : x ∈ V(G)) (hH : x ∈ V(H)),
    D.vertex ⟨x, hG⟩ = D'.vertex ⟨x, hH⟩
  support_inter : D.support ∩ D'.support ⊆
    D.vertex '' {x : V(G) | x.1 ∈ V(H)}

namespace IsFreeUnion

/-- The graph union is defined when the two drawn graphs have disjoint edge sets. -/
theorem compatible (h : D.IsFreeUnion D') : G.Compatible H := by
  sorry

/-- A common support point is a vertex image in both drawings. -/
theorem mem_range_vertex_of_mem_support_inter (h : D.IsFreeUnion D') {z : X}
    (hz : z ∈ D.support) (hz' : z ∈ D'.support) :
    z ∈ range D.vertex ∧ z ∈ range D'.vertex := by
  sorry

/-- The interior of a left edge misses the support of the right drawing. -/
theorem notMem_support_right_of_mem_edgeInterior (h : D.IsFreeUnion D')
    (e : E(G)) {z : X} (hz : z ∈ (D.edgePath e).Interior) : z ∉ D'.support := by
  sorry

/-- The interior of a right edge misses the support of the left drawing. -/
theorem notMem_support_left_of_mem_edgeInterior (h : D.IsFreeUnion D')
    (e : E(H)) {z : X} (hz : z ∈ (D'.edgePath e).Interior) : z ∉ D.support := by
  sorry

end IsFreeUnion

/-- Vertex placement for the union drawing. -/
noncomputable def unionVertex (D : Drawing G X) (D' : Drawing H X)
    (v : V(G ∪ H)) : X := by
  sorry

theorem unionVertex_of_mem_left (D : Drawing G X) (D' : Drawing H X)
    {v : V(G ∪ H)} (hv : v.1 ∈ V(G)) :
    unionVertex D D' v = D.vertex ⟨v.1, hv⟩ := by
  sorry

theorem unionVertex_of_mem_right (h : D.IsFreeUnion D')
    {v : V(G ∪ H)} (hv : v.1 ∈ V(H)) :
    unionVertex D D' v = D'.vertex ⟨v.1, hv⟩ := by
  sorry

/-- Edge placement for the union drawing. -/
noncomputable def unionEdge (h : D.IsFreeUnion D') (e : E(G ∪ H)) :
    Path (unionVertex D D' (edgeSource e)) (unionVertex D D' (edgeTarget e)) := by
  sorry

/-- Glue two freely compatible drawings. -/
noncomputable def union (D : Drawing G X) (D' : Drawing H X)
    (h : D.IsFreeUnion D') : Drawing (G ∪ H) X := by
  sorry

/-- The union drawing restricts to the left drawing. -/
theorem union_extends_left (h : D.IsFreeUnion D') :
    (D.union D' h).Extends D (Graph.left_le_union G H) := by
  sorry

/-- The union drawing restricts to the right drawing. -/
theorem union_extends_right (h : D.IsFreeUnion D') :
    (D.union D' h).Extends D' h.compatible.right_le_union := by
  sorry

/-- The image of a union drawing is the union of the two images. -/
@[simp]
theorem support_union (h : D.IsFreeUnion D') :
    (D.union D' h).support = D.support ∪ D'.support := by
  sorry


end


end Graph.Drawing
