module

public import Matroid.GraphLike.Presentation
public import Matroid.ForMathlib.Geometry.SegmentFigure.Real

/-! # Straight-line graph-like consumers

These checks use the extracted foundation without importing `Graph.Topology.Draft`.
-/

open Set Set.Notation
open scoped GraphLike

section Algebra

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  {G : GraphLike X}

example (hG : G.IsStraightLine) (hV : G.vertexSet.Finite) :
    IsSegmentFigure G.carrier := by
  let : G.Finite := hG.finite_iff.mpr hV
  exact hG.isSegmentFigure_carrier

end Algebra

section Components

variable {X : Type*} [TopologicalSpace X] {G : GraphLike X} {e f : Set X}

-- Edge extensionality works without any vector-space or straightness assumptions.
example (he : e ∈ E(G)) (hf : f ∈ E(G))
    (h : ∀ x, x ∈ G.edgeInterior e ↔ x ∈ G.edgeInterior f) : e = f :=
  G.edge_eq_of_edgeInterior_eq he hf (Set.ext h)

example (h : e = f) : G.edgeBoundary e = G.edgeBoundary f :=
  congrArg G.edgeBoundary h

-- Recognition applies to arbitrary connected sets in graph-like spaces, without geometry.
example {K : Set X} {x y : X} (hK : IsConnected K)
    (hsub : K ⊆ G.carrier \ G.vertexSet) (hxy : x ≠ y)
    (hx : x ∈ G.vertexSet) (hy : y ∈ G.vertexSet)
    (hxK : x ∈ closure K) (hyK : y ∈ closure K) :
    ∃ L ⊆ G.carrier, K ⊆ L ∧ IsPrimitiveLink L x y := by
  obtain ⟨e, he, hi, hb⟩ :=
    G.exists_edge_of_isConnected_of_mem_closure hK hsub hxy hx hy hxK hyK
  exact ⟨e, G.edge_subset he, hi.trans (G.edgeInterior_subset_edge e),
    G.edge_isPrimitiveLink he hb⟩

-- Refinement containment does not require straightness, polygonality, or finiteness.
example {H : GraphLike X} (hGH : G.finer H) {e : Set X} (he : e ∈ E(H)) :
    ∃ f ∈ E(G), e ⊆ f := by
  obtain ⟨f, hf, _⟩ := GraphLike.finer.existsUnique_edge G hGH he
  exact ⟨f, hf.1, hf.2.2⟩

end Components

section LocalSeparation

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [ContinuousAdd X] [ContinuousSMul ℝ X]
  {G H : GraphLike X} {L S F : Set X} {x y a b : X}

-- No ambient Hausdorff instance is supplied in these consumers.
example [T2Space ↥(segment ℝ a b)] (hL : IsPrimitiveLink L x y)
    (hsub : L ⊆ segment ℝ a b) : IsArc L :=
  hL.isArc (hL.endpoints_ne_of_subset_segment hsub)

example [T2Space ↥(segment ℝ a b)] (hL : IsPrimitiveLink L x y)
    (hsub : L ⊆ segment ℝ a b) : Convex ℝ L := by
  rw [hL.eq_segment_of_subset hsub]
  exact convex_segment x y

example (hG : G.IsStraightLine) (hGH : G.finer H) : H.IsPolygonal :=
  (hG.of_finer hGH).isPolygonal

example (hG : G.IsStraightLine) (hxy : x ≠ y)
    (hS : segment ℝ x y ⊆ G.carrier)
    (hV : segment ℝ x y ∩ G.vertexSet = {x, y}) :
    ∃! e : Set X, e ∈ E(G) ∧ e = segment ℝ x y := by
  obtain ⟨e, he, hb⟩ := hG.exists_edge_iff.mpr ⟨hxy, hS, hV⟩
  exact ⟨e, ⟨he, hG he hb⟩, fun f hf ↦ hf.2.trans (hG he hb).symm⟩

-- The presentation retains the marks and supplies compactness with only local separation.
example [T2Space S] (hS : IsSegmentFigure S) (hF : F.Finite) (hFS : F ⊆ S) :
    ∃ G : GraphLike X, G.IsStraightLine ∧ G.carrier = S ∧
      F ⊆ G.vertexSet ∧ IsCompact G.carrier := by
  obtain ⟨G, hfin, hG, hcarrier, hvertices⟩ := hS.exists_straightLineGraphLike hF hFS
  let := hfin
  exact ⟨G, hG, hcarrier, hvertices, G.isCompact⟩

example {ι : Type*} [Finite ι] {S : ι → Set X} [T2Space ↥(⋃ i, S i)]
    (hS : ∀ i, IsSegmentFigure (S i)) : IsCompact (⋃ i, S i) := by
  obtain ⟨G, hfin, _, hcarrier, _⟩ :=
    IsSegmentFigure.exists_common_straightLineGraphLike hS finite_empty (empty_subset _)
  let := hfin
  exact hcarrier ▸ G.isCompact

end LocalSeparation

section Topology

variable {X : Type*} [TopologicalSpace X] [AddCommGroup X] [Module ℝ X]
  [IsTopologicalAddGroup X] [ContinuousSMul ℝ X] [T2Space X]
  {G H : GraphLike X}

-- A geometric segment determines a unique component edge.
example (hG : G.IsStraightLine) {x y : X} (hxy : x ≠ y)
    (hS : segment ℝ x y ⊆ G.carrier)
    (hV : segment ℝ x y ∩ G.vertexSet = {x, y}) :
    ∃! e : Set X, e ∈ E(G) ∧ G.edgeBoundary e = {x, y} := by
  obtain ⟨e, he, hb⟩ := hG.exists_edge_iff.mpr ⟨hxy, hS, hV⟩
  exact ⟨e, ⟨he, hb⟩, fun f hf ↦ hG.edge_eq_of_boundary_eq hf.1 he (hf.2.trans hb.symm)⟩

example (hG : G.IsStraightLine) (hGH : G.finer H) [H.Finite] :
    IsSegmentFigure H.carrier :=
  (hG.of_finer hGH).isSegmentFigure_carrier

-- Point components become vertices, never degenerate edges. This includes the empty figure.
example {F : Set X} (hF : F.Finite) :
    ∃ G : GraphLike X, G.Finite ∧ G.IsStraightLine ∧
      G.carrier = F ∧ G.vertexSet = F ∧ E(G) = ∅ := by
  obtain ⟨G, hfin, hG, hcarrier, hvertices⟩ :=
    (IsSegmentFigure.of_finite hF).exists_straightLineGraphLike hF Subset.rfl
  have hv : G.vertexSet = F :=
    (G.subset.trans hcarrier.subset).antisymm hvertices
  refine ⟨G, hfin, hG, hcarrier, hv, eq_empty_iff_forall_notMem.mpr ?_⟩
  intro e he
  obtain ⟨x, hx⟩ := G.edgeInterior_nonempty he
  have := G.edgeInterior_subset he hx
  simp [hcarrier, hv] at this

-- A crossing, together with an isolated vertex, survives common presentation.
example {a b c d p z : X} (hp : p ∈ segment ℝ a b ∩ segment ℝ c d) :
    ∃ G : GraphLike X, G.Finite ∧ G.IsStraightLine ∧ p ∈ G.vertexSet ∧ z ∈ G.vertexSet ∧
      G.carrier = (segment ℝ a b ∪ {z}) ∪ segment ℝ c d ∧
      segment ℝ a b ∪ {z} =
        ((segment ℝ a b ∪ {z}) ∩ G.vertexSet) ∪
          ⋃ e ∈ {e ∈ E(G) | e ⊆ segment ℝ a b ∪ {z}}, e := by
  let S : Bool → Set X := fun i ↦ if i then segment ℝ a b ∪ {z} else segment ℝ c d
  have hS (i) : IsSegmentFigure (S i) := by
    cases i
    · exact isSegmentFigure_segment _ _
    exact (isSegmentFigure_segment _ _).union (isSegmentFigure_singleton _)
  have hF : ({p, z} : Set X) ⊆ ⋃ i, S i := by
    rintro x (rfl | rfl)
    · exact mem_iUnion.mpr ⟨true, Or.inl hp.1⟩
    · exact mem_iUnion.mpr ⟨true, Or.inr rfl⟩
  obtain ⟨G, hfin, hG, hcarrier, hv, hcover⟩ :=
    IsSegmentFigure.exists_common_straightLineGraphLike hS (by simp) hF
  exact ⟨G, hfin, hG, hv (by simp), hv (by simp),
    hcarrier.trans (by ext x; simp [S, Bool.exists_bool, or_comm, or_assoc]),
    by simpa [S] using hcover true⟩

end Topology

-- Overlapping collinear intervals are preserved as whole-edge supports, not just their union.
example :
    ∃ G : GraphLike ℝ, G.Finite ∧ G.IsStraightLine ∧
      (1 : ℝ) ∈ G.vertexSet ∧ (2 : ℝ) ∈ G.vertexSet ∧
      ∀ i : Bool, (if i then Icc (0 : ℝ) 2 else Icc 1 3) =
        ((if i then Icc (0 : ℝ) 2 else Icc 1 3) ∩ G.vertexSet) ∪
          ⋃ e ∈ {e ∈ E(G) | e ⊆ if i then Icc (0 : ℝ) 2 else Icc 1 3}, e := by
  let S : Bool → Set ℝ := fun i ↦ if i then Icc 0 2 else Icc 1 3
  have hS (i) : IsSegmentFigure (S i) := by
    cases i <;> exact isSegmentFigure_Icc _ _
  have hF : ({1, 2} : Set ℝ) ⊆ ⋃ i, S i := by
    rintro x (rfl | rfl)
    · exact mem_iUnion.mpr ⟨true, by norm_num [S]⟩
    · exact mem_iUnion.mpr ⟨true, by norm_num [S]⟩
  obtain ⟨G, hfin, hG, _, hv, hcover⟩ :=
    IsSegmentFigure.exists_common_straightLineGraphLike hS (by simp) hF
  exact ⟨G, hfin, hG, hv (by simp), hv (by simp), hcover⟩

/-- info: 'IsSegmentFigure.exists_common_straightLineGraphLike' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms IsSegmentFigure.exists_common_straightLineGraphLike

/-- info: 'GraphLike.IsStraightLine.of_finer' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GraphLike.IsStraightLine.of_finer

/-- info: 'GraphLike.IsStraightLine.exists_edge_iff' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms GraphLike.IsStraightLine.exists_edge_iff

