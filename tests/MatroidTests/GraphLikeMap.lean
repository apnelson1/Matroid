module

public import Matroid.GraphLike.MapGeometry
public import Matroid.GraphLike.Presentation

public section

open Set Function Topology
open scoped GraphLike

namespace GraphLikeMapTests

/-- A nonempty one-edge graph-like space for transport tests. -/
theorem exists_segment_graph : ∃ (G : GraphLike ℝ) (e : Set ℝ), e ∈ E(G) ∧
    G.Finite ∧ G.IsStraightLine ∧ G.carrier = segment ℝ 0 1 ∧
    G.vertexSet = {0, 1} ∧ e = segment ℝ 0 1 := by
  obtain ⟨G, q, hfin, hstraight, hc, hv, he⟩ :=
    GraphLike.exists_of_finite_segments ({0, 1} : Set ℝ) (by simp)
      {segment ℝ (0 : ℝ) 1} (finite_singleton _) (by
        intro d hd
        obtain rfl := mem_singleton_iff.mp hd
        exact ⟨0, by simp, 1, by simp, zero_ne_one, rfl, inter_subset_right⟩)
      (by simp)
  refine ⟨G, (q ⟨_, mem_singleton _⟩).1, (q ⟨_, mem_singleton _⟩).2,
    hfin, hstraight, ?_, hv, he _⟩
  rw [hc, sUnion_singleton, union_eq_right]
  exact pair_subset_iff.mpr ⟨left_mem_segment ℝ 0 1, right_mem_segment ℝ 0 1⟩

/-- The transport accepts a map whose behavior away from the carrier collapses points. -/
example : ∃ (G : GraphLike ℝ) (e : Set ℝ) (f : ℝ → ℝ)
    (hf : IsEmbedding (fun x : G.carrier ↦ f x.1)),
    e ∈ E(G) ∧ ¬ Injective f ∧ (G.map f hf).Finite ∧
    f '' e = segment ℝ 0 1 := by
  classical
  obtain ⟨G, e, heG, hfin, _, hc, _, he⟩ := exists_segment_graph
  let f : ℝ → ℝ := fun x ↦ if x ∈ G.carrier then x else 0
  have hf : IsEmbedding (fun x : G.carrier ↦ f x.1) := by
    simpa only [f, Subtype.coe_prop, ite_true] using
      (IsEmbedding.subtypeVal : IsEmbedding (Subtype.val : G.carrier → ℝ))
  refine ⟨G, e, f, hf, heG, ?_, (G.map_finite_iff f hf).mpr hfin, ?_⟩
  · intro hinj
    have h2 : (2 : ℝ) ∉ G.carrier := by rw [hc, segment_eq_Icc (by norm_num)]; norm_num
    have h3 : (3 : ℝ) ∉ G.carrier := by rw [hc, segment_eq_Icc (by norm_num)]; norm_num
    have : (2 : ℝ) = 3 := hinj (by simp [f, h2, h3])
    norm_num at this
  · have hfix : f '' e = e := by
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        simpa [f, G.edge_subset heG hy] using hy
      · intro hx
        exact ⟨x, hx, by simp [f, G.edge_subset heG hx]⟩
    exact hfix.trans he

/-- Distinct edges remain distinct even when their boundary sets coincide. -/
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (G : GraphLike X) (f : X → Y)
    (hf : IsEmbedding (fun x : G.carrier ↦ f x.1))
    (e d : Set X) (he : e ∈ E(G)) (hd : d ∈ E(G))
    (hne : e ≠ d) (hb : G.edgeBoundary e = G.edgeBoundary d) :
    f '' e ≠ f '' d ∧
      (G.map f hf).edgeBoundary (f '' e) = (G.map f hf).edgeBoundary (f '' d) := by
  constructor
  · intro h
    have h' : G.mapEdgeEquiv f hf ⟨e, he⟩ = G.mapEdgeEquiv f hf ⟨d, hd⟩ :=
      Subtype.ext (by simpa only [G.mapEdge_coe] using h)
    exact hne (congrArg Subtype.val ((G.mapEdgeEquiv f hf).injective h'))
  · rw [G.mapEdge_boundary f hf he, G.mapEdge_boundary f hf hd, hb]

/-- Coincident endpoints are retained under carrier embeddings. -/
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (G : GraphLike X) (f : X → Y)
    (hf : IsEmbedding (fun x : G.carrier ↦ f x.1))
    (e : Set X) (he : e ∈ E(G)) (x : X) (hb : G.edgeBoundary e = {x}) :
    (G.map f hf).edgeBoundary (f '' e) = {f x} := by
  rw [G.mapEdge_boundary f hf he, hb, image_singleton]

example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (G : GraphLike X) (f : X → Y)
    (hf : IsEmbedding (fun x : G.carrier ↦ f x.1)) :
    E(G.map f hf) = (Set.image f) '' E(G) := G.map_edgeSet f hf

example {X : Type*} [TopologicalSpace X] (G : GraphLike X) :
    G.map id IsEmbedding.subtypeVal = G := G.map_id _

example {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
    (G : GraphLike X) (f : X → Y) (g : Y → Z)
    (hf : IsEmbedding (fun x : G.carrier ↦ f x.1))
    (hg : IsEmbedding (fun y : (G.map f hf).carrier ↦ g y.1)) :
    (G.map f hf).map g hg = G.map (g ∘ f) (G.map_comp_isEmbedding f hf g hg) :=
  G.map_comp f hf g hg

example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (G : GraphLike X) (f : X → Y)
    (hf : IsEmbedding (fun x : G.carrier ↦ f x.1)) (e : Set X) (he : e ∈ E(G)) :
    f '' e ∈ E(G.map f hf) ∧
      (G.map f hf).edgeInterior (f '' e) = f '' G.edgeInterior e :=
  ⟨by rw [G.map_edgeSet]; exact ⟨e, he, rfl⟩, G.mapEdge_interior f hf he⟩

/-- Affine geometry uses only carrier-local embeddings. -/
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [AddCommGroup X] [Module ℝ X] [AddCommGroup Y] [Module ℝ Y]
    [ContinuousAdd X] [ContinuousSMul ℝ X] [ContinuousAdd Y] [ContinuousSMul ℝ Y]
    (G : GraphLike X) (hG : G.IsStraightLine) (f : X →ᵃ[ℝ] Y)
    (hf : IsEmbedding (fun x : G.carrier ↦ f x.1)) :
    (G.map f hf).IsStraightLine ∧ (G.map f hf).IsPolygonal :=
  ⟨G.map_isStraightLine hG f hf, G.map_isPolygonal hG.isPolygonal f hf⟩

/-- info: 'GraphLike.map' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GraphLike.map
/-- info: 'GraphLike.mapEdgeEquiv' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GraphLike.mapEdgeEquiv
/-- info: 'GraphLike.mapEdge_interior' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GraphLike.mapEdge_interior
/-- info: 'GraphLike.map_edgeSet' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GraphLike.map_edgeSet
/-- info: 'GraphLike.mapEdge_boundary' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GraphLike.mapEdge_boundary
/-- info: 'GraphLike.map_finite_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GraphLike.map_finite_iff
/-- info: 'GraphLike.map_id' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GraphLike.map_id
/-- info: 'GraphLike.map_comp' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GraphLike.map_comp
/-- info: 'GraphLike.map_isStraightLine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GraphLike.map_isStraightLine
/-- info: 'GraphLike.map_isPolygonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GraphLike.map_isPolygonal

end GraphLikeMapTests
