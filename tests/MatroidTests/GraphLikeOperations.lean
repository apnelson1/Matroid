module

import Matroid.GraphLike.MapRestriction
import Matroid.GraphLike.RestrictionGeometry
import MatroidTests.GraphLikeMap

open Set Topology
open scoped GraphLike

namespace GraphLikeOperationsTests

/-- A genuine nondegenerate edge survives restriction with its straight geometry. -/
example : ∃ (G : GraphLike ℝ) (e : Set ℝ), e ∈ E(G) ∧
    (G.restrict ∅ {e}).IsStraightLine ∧ (G.restrict ∅ {e}).IsPolygonal ∧
    (G.restrict ∅ {e}).carrier = segment ℝ 0 1 ∧
    IsSegmentFigure (G.support ∅ {e}) := by
  obtain ⟨G, e, heG, _, hG, _, _, he⟩ := GraphLikeMapTests.exists_segment_graph
  exact ⟨G, e, heG, GraphLike.restrict_isStraightLine hG ∅ {e},
    GraphLike.restrict_isPolygonal hG.isPolygonal ∅ {e},
    by simpa [GraphLike.support, inter_eq_left.mpr (singleton_subset_iff.mpr heG)] using he,
    hG.isSegmentFigure_support ∅ {e} finite_empty (finite_singleton e)⟩

/-- Supports may be finite without any finiteness hypothesis on the original space. -/
example {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
    {G : GraphLike X} (hG : G.IsStraightLine) (v : X) (e : Set X) :
    IsSegmentFigure (G.support {v} {e}) :=
  hG.isSegmentFigure_support {v} {e} (finite_singleton v) (finite_singleton e)

/-- Even an empty restriction obeys transport compatibility. -/
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (G : GraphLike X) (f : X → Y)
    (hf : IsEmbedding (fun x : G.carrier ↦ f x.1)) :
    (G.restrict ∅ ∅).map f (hf.comp (IsEmbedding.inclusion (G.support_subset ∅ ∅))) =
      (G.map f hf).restrict ∅ ∅ := by
  simpa only [empty_inter, image_empty] using G.map_restrict f hf ∅ ∅

/-- A selected edge and vertex commute with transport using only a carrier embedding. -/
example {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (G : GraphLike X) (f : X → Y)
    (hf : IsEmbedding (fun x : G.carrier ↦ f x.1)) (v : X) (e : Set X)
    (hv : v ∈ V(G)) (he : e ∈ E(G)) :
    (G.restrict {v} {e}).map f
        (hf.comp (IsEmbedding.inclusion (G.support_subset {v} {e}))) =
      (G.map f hf).restrict {f v} {f '' e} := by
  simpa only [inter_eq_left.mpr (singleton_subset_iff.mpr hv),
    inter_eq_left.mpr (singleton_subset_iff.mpr he), image_singleton]
    using G.map_restrict f hf {v} {e}

/-- Adjacent segments are exact restrictions of one presentation, with their shared
endpoint retained as a marked vertex. -/
example : ∃ G : GraphLike ℝ, G.Finite ∧ G.IsStraightLine ∧
    G.carrier = ⋃ b : Bool, (if b then segment ℝ (0 : ℝ) 1 else segment ℝ 1 2) ∧
    (1 : ℝ) ∈ G.vertexSet ∧
    ∀ b : Bool,
      (G.restrict (if b then segment ℝ (0 : ℝ) 1 else segment ℝ 1 2)
        {e | e ⊆ (if b then segment ℝ (0 : ℝ) 1 else segment ℝ 1 2)}).carrier =
        (if b then segment ℝ (0 : ℝ) 1 else segment ℝ 1 2) := by
  let S (b : Bool) : Set ℝ := if b then segment ℝ 0 1 else segment ℝ 1 2
  have hS (b : Bool) : IsSegmentFigure (S b) := by
    cases b <;> exact isSegmentFigure_segment _ _
  obtain ⟨G, hfin, hstraight, hc, hv, hr⟩ :=
    IsSegmentFigure.exists_common_straightLineGraphLike_restrictions hS
      (finite_singleton (1 : ℝ)) (by
        intro x hx
        obtain rfl := mem_singleton_iff.mp hx
        exact mem_iUnion.mpr ⟨true, right_mem_segment ℝ 0 1⟩)
  exact ⟨G, hfin, hstraight, hc, hv (mem_singleton _), hr⟩

/-- Raw selections ignore sets that are not edges, without requiring a membership proof. -/
example {X : Type*} [TopologicalSpace X] (G : GraphLike X) :
    G.support ∅ {∅} = ∅ := by
  have he : (∅ : Set X) ∉ E(G) := fun h ↦ (G.edge_nonempty h).ne_empty rfl
  simp [GraphLike.support, he]

/-- Normalization must precede transport: an outside point can map to a vertex. -/
example : ∃ (G : GraphLike ℝ) (f : ℝ → ℝ)
    (hf : IsEmbedding (fun x : G.carrier ↦ f x.1)),
    f '' G.support {2} ∅ = ∅ ∧ f '' ({2} : Set ℝ) = {0} ∧
      (0 : ℝ) ∈ V(G.map f hf) := by
  classical
  obtain ⟨G, _, _, _, _, hc, hv, _⟩ := GraphLikeMapTests.exists_segment_graph
  let f : ℝ → ℝ := fun x ↦ if x ∈ G.carrier then x else 0
  have hf : IsEmbedding (fun x : G.carrier ↦ f x.1) := by
    simpa only [f, Subtype.coe_prop, ite_true] using
      (IsEmbedding.subtypeVal : IsEmbedding (Subtype.val : G.carrier → ℝ))
  have h2 : (2 : ℝ) ∉ G.carrier := by
    rw [hc, segment_eq_Icc (by norm_num)]
    norm_num
  have h2V : (2 : ℝ) ∉ V(G) := fun h ↦ h2 (G.subset h)
  have h0V : (0 : ℝ) ∈ V(G) := hv.symm ▸ (by simp)
  refine ⟨G, f, hf, ?_, ?_, ?_⟩
  · simp [GraphLike.support, h2V]
  · simp [f, h2]
  · exact ⟨0, h0V, by simp [f]⟩

end GraphLikeOperationsTests

/-- info: 'GraphLike.map_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GraphLike.map_support
/-- info: 'GraphLike.map_restrict' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GraphLike.map_restrict
/-- info: 'GraphLike.restrict_isStraightLine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GraphLike.restrict_isStraightLine
/-- info: 'GraphLike.restrict_isPolygonal' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GraphLike.restrict_isPolygonal
/-- info: 'GraphLike.IsStraightLine.isSegmentFigure_support' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms GraphLike.IsStraightLine.isSegmentFigure_support
/-- info: 'IsSegmentFigure.exists_common_straightLineGraphLike_restrictions' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms IsSegmentFigure.exists_common_straightLineGraphLike_restrictions
