import Matroid.Graph.Topology.Defs
import Matroid.GraphLike.Assembly

/-! Regression tests for drawing restriction and carrier-local transport. -/

open Set Function Graph Topology Set.Notation

namespace GraphLikeDrawingOperationsTests

noncomputable section RawEdges

variable {X : Type*} [TopologicalSpace X] (G : GraphLike X)

example : Graph X (Set X) := G.toGraph

example : E(G.toGraph) = G.edgeSet := rfl

example : V(G.toGraph) = G.vertexSet := rfl

example (e : Set X) (x y : X) : G.toGraph.IsLink e x y ↔ G.IsLink e x y := Iff.rfl

example : Drawing X (Set X) X := G.drawing

example (e : G.edgeSet) : G.drawing.edgeRange e = e.1 := rfl

example (e : Set X) (he : e ∉ G.edgeSet) : e ∉ E(G.toGraph) := he

end RawEdges

section General

variable {V E X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (D : Drawing V E X) (K : Graph V E) (hK : K ≤ D.graph)

example : (D.restrict K hK).toGraphLike = D.toGraphLike.restrict
    (range (fun v : V(K) ↦ D.vertex ⟨v.1, hK.vertexSet_mono v.2⟩))
    (range (fun e : E(K) ↦ D.edgeRange ⟨e.1, hK.edgeSet_mono e.2⟩)) :=
  D.restrict_toGraphLike K hK

example : (D.restrict K hK).graph = K := D.restrict_graph K hK

example : (D.restrict K hK).carrier = D.support K hK := D.restrict_carrier K hK

example (v : V(K)) :
    (D.restrict K hK).vertex v = D.vertex ⟨v.1, hK.vertexSet_mono v.2⟩ :=
  D.restrict_vertex K hK v

example (e : E(K)) :
    (D.restrict K hK).edgeRange e = D.edgeRange ⟨e.1, hK.edgeSet_mono e.2⟩ := by simp

/-- Isolated vertices survive even when no edges are selected. -/
example (hE : E(K) = ∅) : (D.restrict K hK).carrier =
    range (fun v : V(K) ↦ D.vertex ⟨v.1, hK.vertexSet_mono v.2⟩) := by
  rw [D.restrict_carrier K hK, Drawing.support]
  have : IsEmpty E(K) := ⟨fun e ↦ by simpa [hE] using e.2⟩
  simp

/-- Empty subgraphs have empty support, without finiteness assumptions. -/
example (hV : V(K) = ∅) (hE : E(K) = ∅) : (D.restrict K hK).carrier = ∅ := by
  rw [D.restrict_carrier K hK, Drawing.support]
  have : IsEmpty V(K) := ⟨fun v ↦ by simpa [hV] using v.2⟩
  have : IsEmpty E(K) := ⟨fun e ↦ by simpa [hE] using e.2⟩
  apply eq_empty_iff_forall_notMem.mpr
  rintro x (⟨v, _⟩ | hx)
  · exact isEmptyElim v
  · obtain ⟨e, _⟩ := mem_iUnion.mp hx
    exact isEmptyElim e

variable (f : X → Y) (hf : IsEmbedding (fun x : D.carrier ↦ f x.1))

example : (D.postcomp f hf).toGraphLike = D.toGraphLike.map f hf :=
  D.postcomp_toGraphLike f hf

example : (D.postcomp f hf).graph = D.graph := D.postcomp_graph f hf

example (v : V(D.graph)) : (D.postcomp f hf).vertex v = f (D.vertex v) :=
  D.postcomp_vertex f hf v

example (e : E(D.graph)) : (D.postcomp f hf).edgeRange e = f '' D.edgeRange e := by simp

/-- Distinct edges remain distinct under each adapter. -/
example (e d : E(K)) (hne : e ≠ d) :
    (D.restrict K hK).edge e ≠ (D.restrict K hK).edge d :=
  (D.restrict K hK).edge.injective.ne hne

example (e d : E(D.graph)) (hne : e ≠ d) :
    (D.postcomp f hf).edge e ≠ (D.postcomp f hf).edge d :=
  (D.postcomp f hf).edge.injective.ne hne

end General

/-- Build a nondegenerate edge instead of relying on an assumed drawing. -/
private theorem interval_edge :
    ∃ (G : GraphLike ℝ) (e : Set ℝ), e ∈ G.edgeSet ∧ e = segment ℝ (0 : ℝ) 1 := by
  let Z : Set ℝ := {0, 1}
  let a (_ : Unit) : Z := ⟨0, by simp [Z]⟩
  let b (_ : Unit) : Z := ⟨1, by simp [Z]⟩
  let q := GraphLike.ofFiniteLinksEdgeEquiv Z
    ((finite_singleton 1).insert 0) a b (fun _ : Unit ↦ segment ℝ (0 : ℝ) 1)
    (fun _ ↦ isPrimitiveLink_segment (by norm_num))
    (fun _ ↦ by
      apply inter_eq_right.mpr
      intro x hx
      rcases hx with rfl | hx
      · exact left_mem_segment ℝ _ _
      · have : x = 1 := hx
        subst x
        exact right_mem_segment ℝ _ _)
    (by intro i j hij; exact False.elim (hij (Subsingleton.elim _ _)))
  exact ⟨_, (q ()).1, (q ()).2, GraphLike.ofFiniteLinksEdgeEquiv_coe ..⟩

/-- A real edge survives both adapters with exactly its original range. -/
example : ∃ (V E : Type) (D : Drawing V E ℝ) (e : E(D.graph)),
    (D.restrict D.graph le_rfl).edgeRange e = segment ℝ (0 : ℝ) 1 ∧
    (D.postcomp id IsEmbedding.subtypeVal).edgeRange e = segment ℝ (0 : ℝ) 1 := by
  obtain ⟨G, e, heG, he⟩ := interval_edge
  let D := G.drawing
  let d : E(D.graph) := D.edge.symm ⟨e, heG⟩
  refine ⟨ℝ, Set ℝ, D, d, ?_, ?_⟩
  · rw [D.restrict_edgeRange]
    change e = _
    exact he
  · rw [D.postcomp_edgeRange]
    change id '' e = _
    simpa only [image_id] using he

open Classical in
/-- No global injectivity is needed: collapse all points outside the drawing's carrier. -/
example {V E : Type*} (D : Drawing V E ℝ) (e : E(D.graph)) :
    let f : ℝ → ℝ := fun x ↦ if x ∈ D.carrier then x else 0
    ∃ hf : IsEmbedding (fun x : D.carrier ↦ f x.1),
      (D.postcomp f hf).edgeRange e = D.edgeRange e := by
  classical
  dsimp only
  let f : ℝ → ℝ := fun x ↦ if x ∈ D.carrier then x else 0
  have hf : IsEmbedding (fun x : D.carrier ↦ f x.1) := by
    simpa only [f, Subtype.coe_prop, ite_true] using
      (IsEmbedding.subtypeVal : IsEmbedding (Subtype.val : D.carrier → ℝ))
  refine ⟨hf, ?_⟩
  rw [D.postcomp_edgeRange]
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa only [ite_eq_left (D.toGraphLike.edge_subset (D.edge e).2 hy)] using hy
  · intro hx
    exact ⟨x, hx, ite_eq_left (D.toGraphLike.edge_subset (D.edge e).2 hx)⟩

end GraphLikeDrawingOperationsTests

/-- info: 'Graph.Drawing.restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graph.Drawing.restrict
/-- info: 'Graph.Drawing.postcomp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graph.Drawing.postcomp
/-- info: 'Graph.Drawing.restrict_toGraphLike' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graph.Drawing.restrict_toGraphLike
/-- info: 'Graph.Drawing.restrict_graph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graph.Drawing.restrict_graph
/-- info: 'Graph.Drawing.restrict_carrier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graph.Drawing.restrict_carrier
/-- info: 'Graph.Drawing.restrict_vertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graph.Drawing.restrict_vertex
/-- info: 'Graph.Drawing.restrict_vertexSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graph.Drawing.restrict_vertexSet
/-- info: 'Graph.Drawing.restrict_edgeRange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graph.Drawing.restrict_edgeRange
/-- info: 'Graph.Drawing.postcomp_toGraphLike' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graph.Drawing.postcomp_toGraphLike
/-- info: 'Graph.Drawing.postcomp_graph' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graph.Drawing.postcomp_graph
/-- info: 'Graph.Drawing.postcomp_carrier' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graph.Drawing.postcomp_carrier
/-- info: 'Graph.Drawing.postcomp_vertexSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graph.Drawing.postcomp_vertexSet
/-- info: 'Graph.Drawing.postcomp_vertex' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graph.Drawing.postcomp_vertex
/-- info: 'Graph.Drawing.postcomp_edgeRange' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Graph.Drawing.postcomp_edgeRange
