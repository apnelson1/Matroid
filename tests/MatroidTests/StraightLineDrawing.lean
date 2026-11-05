import Matroid.Graph.Topology.StraightLine

open Set Graph Set.Notation

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]

example {V E : Type*} (D : Drawing V E X) (hD : D.toGraphLike.IsStraightLine)
    {e : E(D.graph)} {u v : V(D.graph)} (h : D.graph.IsLink e.1 u.1 v.1) :
    D.edgeRange e = segment ℝ (D.vertex u) (D.vertex v) :=
  D.edgeRange_eq_segment hD h

example (G : GraphLike X) (hG : G.IsStraightLine) {e : Set X}
    (he : e ∈ G.edgeSet) {x y : X} (h : G.IsLink e x y) :
    G.drawing.edgeRange ⟨e, he⟩ = segment ℝ x y := by
  exact G.drawing.edgeRange_eq_segment hG
    (e := ⟨e, he⟩) (u := ⟨x, h.left_mem⟩) (v := ⟨y, h.right_mem⟩) h

/-- info: 'Graph.Drawing.edgeRange_eq_segment' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graph.Drawing.edgeRange_eq_segment
