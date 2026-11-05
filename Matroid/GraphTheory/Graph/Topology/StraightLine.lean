import Matroid.GraphTheory.Graph.Topology.Defs
import Matroid.GraphTheory.GraphTopology.StraightLine

/-! # Straight-line drawings -/

open Set Graph Set.Notation

variable {V E X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]

/-- In a straight-line drawing, incidence determines the segment traced by an edge. -/
theorem Graph.Drawing.edgeRange_eq_segment (D : Drawing V E X)
    (hD : D.toGraphLike.IsStraightLine) {e : E(D.graph)} {u v : V(D.graph)}
    (h : D.graph.IsLink e.1 u.1 v.1) :
    D.edgeRange e = segment ℝ (D.vertex u) (D.vertex v) :=
  hD (D.edge e).2 (D.iso.map_isLink h).2
