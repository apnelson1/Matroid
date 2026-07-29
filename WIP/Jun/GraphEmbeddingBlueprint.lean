import Matroid.Binary.Representation
import Matroid.ForMathlib.Data.Set.IndexedPartition
import Matroid.Graph.Planarity.K33
import Matroid.Graph.Planarity.Realization.Celluar
import Matroid.Graph.Planarity.Realization.Metric
import Matroid.Minor.Iso
import Matroid.Tame
import Mathlib.Order.UpperLower.Basic
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Order

/-!
# Blueprint: graph-like spaces, realizations, and geometric duality

This file is deliberately outside the `Matroid` build path.  It is a design document that Lean
checks.  Definitions in the first half are intended to be stable interfaces; the theorems ending
in `sorry` are the proposed milestones.

The definition of `GraphLikeSpace` follows Bowler--Carmesin--Christian, *Infinite graphic
matroids*, Definition 3.1.  In particular:

* compactness and metrizability are **not** part of a graph-like space;
* vertices and edges are structure, rather than properties recovered from the point-set topology;
* the open edge interiors are distinguished and disjoint;
* distinct vertices can be separated by disjoint open sets which partition all vertices.

This avoids the two main traps in the old `GraphContinuum` draft: recovering edges as path
components, and assuming an extended metric before the graph-like structure has been specified.
-/

open Function Set Topology TopologicalSpace
open scoped unitInterval Sym2

universe u v w

namespace GraphEmbeddingBlueprint

/-! ## 1. The basic graph-like-space interface -/

/--
An indexed partition of a distinguished vertex type.  Keeping this independent of
`GraphLikeSpace` lets the graph-like-space separation axiom itself use the common partition
interface.
-/
abbrev IndexedVertexPartition (V : Type v) (ι : Type*) := (Set.univ : Set V).IndexedPartition ι

/--
The parts of `P` are the traces on the vertices of pairwise-disjoint ambient-open sets.  The
ambient sets may also contain edge-interior points.
-/
def IsOpenRealizableVertexPartition {Point : TopCat.{u}} {V : Type v} {ι : Type*}
    (vertex : V ↪ Point) (P : IndexedVertexPartition V ι) : Prop :=
  ∃ U : ι → Set Point, (∀ i, IsOpen (U i)) ∧ Pairwise (Disjoint on U) ∧
    ∀ i v, vertex v ∈ U i ↔ v ∈ P i

namespace IndexedVertexPartition

/-- Two vertices lie in distinct cells of an indexed vertex partition. -/
def Separates {V : Type v} {ι : Type*} (P : IndexedVertexPartition V ι) (v w : V) : Prop :=
  ∃ i j, i ≠ j ∧ v ∈ P i ∧ w ∈ P j

end IndexedVertexPartition

/-- The open parameter interval used for edge interiors. -/
abbrev OpenUnitInterval := Set.Ioo (0 : ℝ) 1

/-- Regard an interior parameter as a point of the closed unit interval. -/
def openToUnitInterval (t : OpenUnitInterval) : I := ⟨t.1, le_of_lt t.2.1, le_of_lt t.2.2⟩

/--
A graph-like space.  `Point` is bundled with its topology so that two different topologies on the
same carrier can coexist without typeclass diamonds.

The edge paths are oriented only for bookkeeping.  Reversing one of them does not change the
underlying graph-like space.
-/
structure GraphLikeSpace where
  Point : TopCat.{u}
  Vertex : Type v
  Edge : Type w
  vertex : Vertex ↪ Point
  source : Edge → Vertex
  target : Edge → Vertex
  edgePath : (e : Edge) → Path (vertex (source e)) (vertex (target e))
  edgeInterior_openEmbedding : ∀ e, IsOpenEmbedding
      (fun t : OpenUnitInterval => edgePath e (openToUnitInterval t))
  edgeInteriors_disjoint : ∀ ⦃e f⦄, e ≠ f → Disjoint
      (range (fun t : OpenUnitInterval => edgePath e (openToUnitInterval t)))
        (range (fun t : OpenUnitInterval => edgePath f (openToUnitInterval t)))
  vertices_disjoint_edgeInteriors : ∀ e, Disjoint (range vertex)
      (range (fun t : OpenUnitInterval => edgePath e (openToUnitInterval t)))
  point_eq_vertex_or_edgeInterior : range vertex ∪
      ⋃ e, range (fun t : OpenUnitInterval => edgePath e (openToUnitInterval t)) = univ
  separate_vertices : ∀ ⦃v w⦄, v ≠ w → ∃ P : IndexedVertexPartition Vertex Bool,
        IsOpenRealizableVertexPartition vertex P ∧ P.Separates v w

namespace GraphLikeSpace

variable (X : GraphLikeSpace.{u,v,w})

/-- The open interior of an edge as a subset of the point space. -/
def edgeInterior (e : X.Edge) : Set X.Point :=
  range (fun t : OpenUnitInterval => X.edgePath e (openToUnitInterval t))

/-- The distinguished vertex set as a subset of the point space. -/
def vertexSet : Set X.Point := range X.vertex

/-- Compactness is an optional property, not part of `GraphLikeSpace`. -/
def IsCompact : Prop := _root_.IsCompact (univ : Set X.Point)

/-- Metrizability is an optional property, not part of `GraphLikeSpace`. -/
def IsMetrizable : Prop := MetrizableSpace X.Point

/-- A graph-like continuum is compact, metrizable, and connected. -/
def IsContinuum : Prop := X.IsCompact ∧ X.IsMetrizable ∧ IsConnected (univ : Set X.Point)

/-- The abstract incidence graph obtained by forgetting the topology. -/
def incidenceGraph : Graph X.Vertex X.Edge where
  vertexSet := univ
  edgeSet := univ
  IsLink e v w := s(v, w) = s(X.source e, X.target e)
  isLink_symm e _ := ⟨fun a b hab => by simpa only [Sym2.eq_swap] using hab⟩
  eq_or_eq_of_isLink_of_isLink e a b c d hab hcd := by
    have h := Sym2.eq_iff.mp (hab.trans hcd.symm)
    exact h.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  edge_mem_iff_exists_isLink e := by
    simp only [mem_univ, true_iff]
    exact ⟨X.source e, X.target e, rfl⟩
  left_mem_of_isLink e := by simp

/-! ### Maps -/

/-- The image of an edge under a graph-like map: an oriented edge, or a collapsed vertex. -/
inductive EdgeImage (Y : GraphLikeSpace.{u,v,w}) where
  | edge (edge : Y.Edge) (reverse : Bool)
  | vertex (vertex : Y.Vertex)

/-- Reverse the unit-interval parameter when an oriented edge is mapped backwards. -/
def orientedParameter (reverse : Bool) (t : I) : I := if reverse then unitInterval.symm t else t

/--
A map of graph-like spaces in the sense of Bowler--Carmesin--Christian.

Storing `pointMap` makes continuity easy to use.  The last two fields say that it is exactly the
function induced by the vertex and edge data, rather than an unrelated continuous map.
-/
structure Hom (X Y : GraphLikeSpace.{u,v,w}) where
  vertexMap : X.Vertex → Y.Vertex
  edgeMap : X.Edge → EdgeImage Y
  pointMap : X.Point → Y.Point
  continuous_pointMap : Continuous pointMap
  map_vertex : ∀ v, pointMap (X.vertex v) = Y.vertex (vertexMap v)
  map_edge : ∀ e t, pointMap (X.edgePath e t) = match edgeMap e with
    | .edge f reverse => Y.edgePath f (orientedParameter reverse t)
    | .vertex v => Y.vertex v

/-- A graph-like embedding remembers the induced injection on edges explicitly. -/
structure Embedding (X Y : GraphLikeSpace.{u,v,w}) extends Hom X Y where
  pointMap_injective : Injective pointMap
  edgeEmbedding : X.Edge ↪ Y.Edge
  edgeReverse : X.Edge → Bool
  edgeMap_eq : ∀ e, edgeMap e = .edge (edgeEmbedding e) (edgeReverse e)

/-! ### Topological cuts, bonds, and contraction -/

/-- An indexed partition of all the vertices of `X`. -/
abbrev VertexPartition (ι : Type*) := IndexedVertexPartition X.Vertex ι

/-- A labelled bipartition of all the vertices of `X`. -/
abbrev VertexBipartition := X.VertexPartition Bool

namespace VertexPartition

variable {X} {ι : Type*}

/--
The indexed vertex partition is represented by pairwise-disjoint ambient-open sets.  This is a
property of a partition rather than extra data: different choices of ambient neighbourhoods do
not create different separations.
-/
def HasOpenRealization (P : X.VertexPartition ι) : Prop :=
  IsOpenRealizableVertexPartition X.vertex P

/-- Whether two vertices lie in distinct cells of the partition. -/
def Separates (P : X.VertexPartition ι) (v w : X.Vertex) : Prop :=
  IndexedVertexPartition.Separates P v w

end VertexPartition

namespace VertexBipartition

variable {X}

/-- The set of edges whose endvertices lie in distinct cells of `P`. -/
def edgeBoundary (P : X.VertexBipartition) : Set X.Edge :=
    {e | VertexPartition.Separates P (X.source e) (X.target e)}

end VertexBipartition

/-- A topological cut is induced by an ambient-open partition of the vertices. -/
def IsTopologicalCut (C : Set X.Edge) : Prop := ∃ P : X.VertexBipartition,
    VertexPartition.HasOpenRealization P ∧ P.edgeBoundary = C

/-- A topological bond is an inclusion-minimal nonempty topological cut. -/
def IsTopologicalBond (B : Set X.Edge) : Prop :=
  Minimal (fun C : Set X.Edge => C.Nonempty ∧ X.IsTopologicalCut C) B

/--
The vertex equivalence relation used when contracting `C`: two vertices are identified exactly
when every topological cut separating them meets `C`.
-/
def ContractVertexRel (C : Set X.Edge) (v w : X.Vertex) : Prop := ∀ P : X.VertexBipartition,
    VertexPartition.HasOpenRealization P → VertexPartition.Separates P v w →
    (P.edgeBoundary ∩ C).Nonempty

/--
A vertex cannot be separated from itself.  This is the disjointness step in reflexivity of
`ContractVertexRel`.
-/
theorem VertexPartition.not_separates_self {ι : Type*} (P : X.VertexPartition ι) (v : X.Vertex) :
    ¬ VertexPartition.Separates P v v := by
  sorry

/-- Separation by an indexed partition is symmetric in the two vertices. -/
theorem VertexPartition.separates_comm {ι : Type*} (P : X.VertexPartition ι) (v w : X.Vertex) :
    VertexPartition.Separates P v w ↔ VertexPartition.Separates P w v := by
  sorry

/--
If `P` separates `v` from `z`, an intermediate vertex `w` is separated from at least one of
them.  This is the only combinatorial observation needed for transitivity of contraction.
-/
theorem VertexPartition.separates_left_or_right {ι : Type*} (P : X.VertexPartition ι)
    {v w z : X.Vertex} (hvz : VertexPartition.Separates P v z) :
    VertexPartition.Separates P v w ∨ VertexPartition.Separates P w z := by
  sorry

theorem contractVertexRel_equivalence (C : Set X.Edge) : Equivalence (X.ContractVertexRel C) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v P _ hP
    exact (VertexPartition.not_separates_self (X := X) P v hP).elim
  · intro v w hvw P hP hwv
    exact hvw P hP ((VertexPartition.separates_comm (X := X) P v w).2 hwv)
  · intro v w z hvw hwz P hP hvz
    exact (VertexPartition.separates_left_or_right (X := X) P hvz).elim (hvw P hP) (hwz P hP)

/-- The setoid on vertices determined by contraction of `C`. -/
noncomputable def contractVertexSetoid (C : Set X.Edge) : Setoid X.Vertex :=
    ⟨X.ContractVertexRel C, X.contractVertexRel_equivalence C⟩

/-- Vertices of the quotient model for `X / C`. -/
abbrev ContractVertex (C : Set X.Edge) := Quotient (X.contractVertexSetoid C)

/--
The endpoints of an edge in `C` are equivalent for the topological contraction relation: every
open vertex bipartition separating them has that edge in its boundary.
-/
theorem contractVertexRel_source_target_of_mem (C : Set X.Edge) {e : X.Edge} (he : e ∈ C) :
    X.ContractVertexRel C (X.source e) (X.target e) := by
  sorry

/--
One generating identification for point-space contraction.  The first alternative collapses a
closed edge of `C` to its source class.  The second inserts the full topological equivalence
relation on vertices.

That second alternative is essential.  `ContractVertexRel` need not be merely finite
edge-connectivity in `C`: limit vertices can fail to be separated by any topological cut
disjoint from `C`.  Using only the equivalence closure of closed `C`-edges would therefore
construct the wrong quotient.
-/
def ContractPointStep (C : Set X.Edge) (x y : X.Point) : Prop :=
    (∃ (e : X.Edge) (_he : e ∈ C) (t : I), x = X.edgePath e t ∧ y = X.vertex (X.source e)) ∨
    ∃ v w : X.Vertex, X.ContractVertexRel C v w ∧ x = X.vertex v ∧ y = X.vertex w

/--
The equivalence relation generated by collapsing the closed edges in `C` and by the topological
vertex equivalence.  Surviving open-edge points have singleton classes.
-/
def ContractPointRel (C : Set X.Edge) : X.Point → X.Point → Prop :=
  Relation.EqvGen (X.ContractPointStep C)

/-- The point setoid for contraction. -/
def contractPointSetoid (C : Set X.Edge) : Setoid X.Point :=
  Relation.EqvGen.setoid (X.ContractPointStep C)

/-- Point space of the quotient model for `X / C`, with its quotient topology. -/
abbrev ContractPoint (C : Set X.Edge) := Quotient (X.contractPointSetoid C)

/-- The two contraction relations agree on embedded vertices. -/
theorem contractPointRel_vertex_iff (C : Set X.Edge) (v w : X.Vertex) :
    X.ContractPointRel C (X.vertex v) (X.vertex w) ↔ X.ContractVertexRel C v w := by
  sorry

/-- The canonical inclusion of quotient vertices into the contracted point quotient. -/
noncomputable def contractVertexToPoint (C : Set X.Edge) : X.ContractVertex C → X.ContractPoint C :=
  Quotient.lift (fun v => Quotient.mk' (s := X.contractPointSetoid C) (X.vertex v))
    (fun v w h => Quotient.sound ((X.contractPointRel_vertex_iff C v w).2 h))

/-- Distinct quotient vertices remain distinct as points of the contraction. -/
theorem contractVertexToPoint_injective (C : Set X.Edge) :
    Injective (X.contractVertexToPoint C) := by
  sorry

/--
No new identifications occur between interior points of edges outside `C`.  This is where the
topological-cut characterization of `ContractVertexRel` is used.
-/
theorem contractPointRel_surviving_interiors_iff (C : Set X.Edge) {e f : X.Edge} (he : e ∉ C)
    (hf : f ∉ C) (s t : OpenUnitInterval) : X.ContractPointRel C
        (X.edgePath e (openToUnitInterval s)) (X.edgePath f (openToUnitInterval t)) ↔
      e = f ∧ s = t := by
  sorry

/--
After passing to the quotient topology, every surviving open edge is still an open embedding.
The proof uses the preceding exact-fibre lemma and saturates a small open interval away from the
contracted edge fibres.
-/
theorem contract_surviving_edge_openEmbedding (C : Set X.Edge) (e : {e : X.Edge // e ∉ C}) :
    IsOpenEmbedding (fun t : OpenUnitInterval =>
        Quotient.mk' (s := X.contractPointSetoid C) (X.edgePath e.1 (openToUnitInterval t))) := by
  sorry

/--
The quotient vertices retain the graph-like separation axiom.  A separating open partition
upstairs can be chosen saturated because its edge boundary avoids `C`, and quotient openness then
gives the required partition downstairs.
-/
theorem contract_vertices_have_open_separations (C : Set X.Edge) :
    ∀ ⦃v w : X.ContractVertex C⦄, v ≠ w → ∃ P : IndexedVertexPartition (X.ContractVertex C) Bool,
        IsOpenRealizableVertexPartition (Point := TopCat.of (X.ContractPoint C))
          (⟨X.contractVertexToPoint C, X.contractVertexToPoint_injective C⟩ :
            X.ContractVertex C ↪ X.ContractPoint C) P ∧
          P.Separates v w := by
  sorry

/-- Data exhibiting `q : X → Y` as contraction of precisely the edge set `C`. -/
structure IsContractionModel (C : Set X.Edge) (Y : GraphLikeSpace.{u,v,w}) (q : Hom X Y) where
  quotientMap : IsQuotientMap q.pointMap
  edgeEquiv : {e : X.Edge // e ∉ C} ≃ Y.Edge
  edgeReverse : {e : X.Edge // e ∉ C} → Bool
  edgeMap_of_notMem : ∀ e : {e : X.Edge // e ∉ C},
    q.edgeMap e.1 = .edge (edgeEquiv e) (edgeReverse e)
  edgeMap_of_mem : ∀ e (_he : e ∈ C), ∃ v, q.edgeMap e = .vertex v
  vertexMap_eq_iff : ∀ v w, q.vertexMap v = q.vertexMap w ↔ X.ContractVertexRel C v w

/--
Assembly lemma for contraction.  The quotient carrier, quotient vertices, surviving edge paths,
and the preceding fibre/separation lemmas satisfy every field of `GraphLikeSpace` and
`IsContractionModel`.
-/
theorem contract_quotient_assembles_model (C : Set X.Edge) :
    ∃ (Y : GraphLikeSpace.{u,v,w}) (q : Hom X Y), Nonempty (X.IsContractionModel C Y q) := by
  sorry

/-- Milestone: construct the quotient graph-like space `X / C` with the quotient topology. -/
theorem exists_contraction (C : Set X.Edge) : ∃ (Y : GraphLikeSpace.{u,v,w}) (q : Hom X Y),
      Nonempty (X.IsContractionModel C Y q) := by
  exact X.contract_quotient_assembles_model C

/-! ### Restrictions and standard subspaces -/

/--
The point set of the restriction to `R`.  All original vertices are retained, including spurious
vertices not incident with an edge of `R`, exactly as in the graph-like-space literature.
-/
def restrictionPointSet (R : Set X.Edge) : Set X.Point := X.vertexSet ∪ ⋃ e : R, X.edgeInterior e

/--
The standard subspace on `R` discards spurious vertices: it is the closure of the selected open
edge interiors.  Keeping this distinct from `restrictionPointSet` prevents later ambiguity.
-/
def standardSubspacePointSet (R : Set X.Edge) : Set X.Point := closure (⋃ e : R, X.edgeInterior e)

/-- The subtype carrying the restriction topology. -/
abbrev RestrictionPoint (R : Set X.Edge) := X.restrictionPointSet R

/-- Every original vertex is present in the restriction point set. -/
theorem vertex_mem_restrictionPointSet (R : Set X.Edge) (v : X.Vertex) :
    X.vertex v ∈ X.restrictionPointSet R := by
  sorry

/-- Every point of a selected open edge is present in the restriction point set. -/
theorem edgeInterior_subset_restrictionPointSet (R : Set X.Edge) (e : R) :
    X.edgeInterior e.1 ⊆ X.restrictionPointSet R := by
  sorry

/-- The original vertex embedding, lifted to the restriction subtype. -/
def restrictionVertexEmbedding (R : Set X.Edge) : X.Vertex ↪ X.RestrictionPoint R where
  toFun v := ⟨X.vertex v, X.vertex_mem_restrictionPointSet R v⟩
  inj' _ _ h := X.vertex.injective (congrArg Subtype.val h)

/-- Selected edge paths lift continuously to the restriction subtype, including their endpoints. -/
theorem exists_restriction_edgePath_lift (R : Set X.Edge) (e : R) : ∃ γ : Path
        (⟨X.vertex (X.source e.1), X.vertex_mem_restrictionPointSet R _⟩ : X.RestrictionPoint R)
        (⟨X.vertex (X.target e.1), X.vertex_mem_restrictionPointSet R _⟩ : X.RestrictionPoint R),
      (fun t => (γ t : X.Point)) = X.edgePath e.1 := by
  sorry

/-- Open edge interiors remain open embeddings after restriction to the subtype. -/
theorem restriction_edgeInterior_openEmbedding (R : Set X.Edge) (e : R) : ∃ γ : Path
        (⟨X.vertex (X.source e.1), X.vertex_mem_restrictionPointSet R _⟩ : X.RestrictionPoint R)
        (⟨X.vertex (X.target e.1), X.vertex_mem_restrictionPointSet R _⟩ : X.RestrictionPoint R),
      IsOpenEmbedding (fun t : OpenUnitInterval => γ (openToUnitInterval t)) := by
  sorry

/--
Intersecting an ambient-open realization of a vertex partition with the restriction subtype
preserves its vertex trace and pairwise disjointness.
-/
theorem restriction_preserves_open_vertexPartition (R : Set X.Edge) {ι : Type*}
    (P : X.VertexPartition ι) (hP : VertexPartition.HasOpenRealization P) :
    IsOpenRealizableVertexPartition (Point := TopCat.of (X.RestrictionPoint R))
      (X.restrictionVertexEmbedding R) P := by
  sorry

/-- Data exhibiting `Y` as the restriction of `X` to `R`. -/
structure IsRestrictionModel (R : Set X.Edge) (Y : GraphLikeSpace.{u,v,w}) where
  inclusion : Embedding Y X
  vertexEquiv : Y.Vertex ≃ X.Vertex
  edgeEquiv : Y.Edge ≃ R
  vertexMap_eq : ∀ v, inclusion.vertexMap v = vertexEquiv v
  edgeEmbedding_eq : ∀ e, inclusion.edgeEmbedding e = (edgeEquiv e).1
  point_range : range inclusion.pointMap = X.restrictionPointSet R

/--
Assembly lemma for restriction.  Use the subtype topology, retain all vertices, index the edges
by `R`, and lift each selected path using the preceding lemmas.
-/
theorem restriction_subtype_assembles_model (R : Set X.Edge) :
    ∃ Y : GraphLikeSpace.{u,v,w}, Nonempty (X.IsRestrictionModel R Y) := by
  sorry

/-- Milestone: restriction to any edge set is again a graph-like space. -/
theorem exists_restriction (R : Set X.Edge) :
    ∃ Y : GraphLikeSpace.{u,v,w}, Nonempty (X.IsRestrictionModel R Y) := by
  exact X.restriction_subtype_assembles_model R

end GraphLikeSpace

/-! ## 2. Canonical pseudo-lines and pseudo-circles -/

namespace OrderedPseudoLine

variable (P : Type u) [LinearOrder P]

/-- Vertices of the pseudo-line `L(P)` are all lower (initial) segments of `P`. -/
abbrev Vertex := LowerSet P

/-- Its underlying set is the vertices plus one open interval for each element of `P`. -/
abbrev Point := Vertex P ⊕ (OpenUnitInterval × P)

def before (p : P) : Vertex P := ⟨Iio p, isLowerSet_Iio p⟩
def through (p : P) : Vertex P := ⟨Iic p, isLowerSet_Iic p⟩
def start : Vertex P := ⟨∅, isLowerSet_empty⟩
def finish : Vertex P := ⟨univ, isLowerSet_univ⟩

/-- The subbasic set `S(p,r)⁻` from Definition 4.1. -/
def minus (p : P) (r : OpenUnitInterval) : Set (Point P) := {x | match x with
    | .inl v => p ∉ v.carrier
    | .inr q => q.2 < p ∨ (q.2 = p ∧ (q.1 : ℝ) < r)}

/-- The subbasic set `S(p,r)⁺` from Definition 4.1. -/
def plus (p : P) (r : OpenUnitInterval) : Set (Point P) := {x | match x with
    | .inl v => p ∈ v.carrier
    | .inr q => p < q.2 ∨ (q.2 = p ∧ (r : ℝ) < q.1)}

def subbasis : Set (Set (Point P)) := {U | ∃ p r, U = minus P p r ∨ U = plus P p r}

/-- The topology generated by the `S(p,r)⁻` and `S(p,r)⁺` subbasis. -/
@[instance_reducible]
def topology : TopologicalSpace (Point P) := TopologicalSpace.generateFrom (subbasis P)

instance : TopologicalSpace (Point P) := topology P

/-- The raw parametrization of the edge indexed by `p`. -/
noncomputable def edgeParam (p : P) (t : I) : Point P := if h0 : t = 0 then .inl (before P p)
  else if h1 : t = 1 then .inl (through P p)
  else
    have ht0 : (0 : ℝ) < t := lt_of_le_of_ne t.2.1 (by
      intro h
      apply h0
      exact Subtype.ext h.symm)
    have ht1 : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2 (by
      intro h
      apply h1
      exact Subtype.ext h)
    .inr (⟨t, ht0, ht1⟩, p)

@[simp] theorem edgeParam_zero (p : P) : edgeParam P p 0 = .inl (before P p) := by
  simp [edgeParam]

@[simp] theorem edgeParam_one (p : P) : edgeParam P p 1 = .inl (through P p) := by
  simp [edgeParam]

/-- Away from the endpoints, the edge parametrization is the evident tagged interior point. -/
theorem edgeParam_openToUnitInterval (p : P) (t : OpenUnitInterval) :
    edgeParam P p (openToUnitInterval t) = .inr (t, p) := by
  sorry

/--
The inverse image of every generating subbasic open set under an edge parametrization is open in
the unit interval.  There are four order cases according to the two edge indices.
-/
theorem isOpen_edgeParam_preimage_of_mem_subbasis (p : P) {U : Set (Point P)} (hU : U ∈ subbasis P)
    : IsOpen (edgeParam P p ⁻¹' U) := by
  sorry

/--
Continuity into a `generateFrom` topology follows by checking inverse images on the declared
subbasis.
-/
theorem continuous_edgeParam_of_subbasis (p : P) : Continuous (edgeParam P p) := by
  sorry

theorem continuous_edgeParam (p : P) : Continuous (edgeParam P p) :=
  continuous_edgeParam_of_subbasis P p

/-- The open part of an edge is literally the corresponding tagged interval and is open. -/
theorem edgeInterior_openEmbedding (p : P) : IsOpenEmbedding
      (fun t : OpenUnitInterval => edgeParam P p (openToUnitInterval t)) := by
  sorry

/-- Different edge tags have disjoint open interiors. -/
theorem edgeInteriors_disjoint ⦃p q : P⦄ (hpq : p ≠ q) : Disjoint
      (range (fun t : OpenUnitInterval => edgeParam P p (openToUnitInterval t)))
      (range (fun t : OpenUnitInterval => edgeParam P q (openToUnitInterval t))) := by
  sorry

/-- A tagged open-edge point is never a lower-set vertex. -/
theorem vertices_disjoint_edgeInteriors (p : P) : Disjoint (range (Sum.inl : Vertex P → Point P))
      (range (fun t : OpenUnitInterval => edgeParam P p (openToUnitInterval t))) := by
  sorry

/-- Every point is either a lower-set vertex or a uniquely tagged edge-interior point. -/
theorem vertex_or_edgeInterior_covers : range (Sum.inl : Vertex P → Point P) ∪
      ⋃ p, range (fun t : OpenUnitInterval => edgeParam P p (openToUnitInterval t)) = univ := by
  sorry

/--
Two different lower sets differ at some order element.  The associated `minus` and `plus`
subbasic opens give the required indexed vertex bipartition.
-/
theorem exists_open_vertexBipartition
    ⦃v w : Vertex P⦄ (hvw : v ≠ w) : ∃ Q : IndexedVertexPartition (Vertex P) Bool,
      IsOpenRealizableVertexPartition (Point := TopCat.of (Point P))
        (⟨Sum.inl, Sum.inl_injective⟩ : Vertex P ↪ Point P) Q ∧
      Q.Separates v w := by
  sorry

/-- The exact ordered construction is a graph-like space. -/
noncomputable def space : GraphLikeSpace.{u,u,u} where
  Point := TopCat.of (Point P)
  Vertex := Vertex P
  Edge := P
  vertex := ⟨Sum.inl, Sum.inl_injective⟩
  source := before P
  target := through P
  edgePath p :=
    { toFun := edgeParam P p
      source' := edgeParam_zero P p
      target' := edgeParam_one P p
      continuous_toFun := continuous_edgeParam P p }
  edgeInterior_openEmbedding := edgeInterior_openEmbedding P
  edgeInteriors_disjoint := fun _ _ h => edgeInteriors_disjoint P h
  vertices_disjoint_edgeInteriors := vertices_disjoint_edgeInteriors P
  point_eq_vertex_or_edgeInterior := vertex_or_edgeInterior_covers P
  separate_vertices := exists_open_vertexBipartition P

/--
Every cover of `L(P)` by members of the defining subbasis has a finite subcover.  If not, the
uncovered `minus` sets and uncovered `plus` sets determine a lower cut of `P`; the vertex
representing that cut is then uncovered.
-/
theorem subbasis_cover_has_finite_subcover (𝒰 : Set (Set (Point P))) (hsub : 𝒰 ⊆ subbasis P)
    (hcover : ⋃₀ 𝒰 = univ) : ∃ 𝒱 : Set (Set (Point P)), 𝒱 ⊆ 𝒰 ∧ 𝒱.Finite ∧ ⋃₀ 𝒱 = univ := by
  sorry

/--
Alexander's subbase theorem, applied to the preceding finite-subcover statement, makes the
ordered pseudo-line compact.
-/
theorem pointSpace_compact : _root_.IsCompact (univ : Set (Point P)) := by
  sorry

theorem space_compact : (space P).IsCompact := by
  exact pointSpace_compact P

/--
A clopen set containing one endpoint of an edge contains the other endpoint: the edge path has
connected image.
-/
theorem clopen_mem_before_iff_mem_through (U : Set (Point P)) (hUo : IsOpen U) (hUc : IsClosed U)
    (p : P) : Sum.inl (before P p) ∈ U ↔ Sum.inl (through P p) ∈ U := by
  sorry

/--
There is no nontrivial clopen subset.  Propagating membership across every edge makes the
vertices in the set a lower cut with no boundary; evaluating at that cut forces it to be either
the empty or full cut.
-/
theorem clopen_eq_empty_or_univ (U : Set (Point P)) (hUo : IsOpen U) (hUc : IsClosed U) :
    U = ∅ ∨ U = univ := by
  sorry

/-- The clopen characterization of connectedness applied to the preceding lemma. -/
theorem pointSpace_connected : IsConnected (univ : Set (Point P)) := by
  sorry

theorem space_connected : IsConnected (univ : Set (space P).Point) := by
  exact pointSpace_connected P

end OrderedPseudoLine

namespace OrderedPseudoCircle

variable (P : Type u) [LinearOrder P] [Nonempty P]

/-- Identify only the start and finish vertices of `L(P)`. -/
def VertexRel (x y : OrderedPseudoLine.Vertex P) : Prop := x = y ∨
  (x = OrderedPseudoLine.start P ∧ y = OrderedPseudoLine.finish P) ∨
  (x = OrderedPseudoLine.finish P ∧ y = OrderedPseudoLine.start P)

/-- Reflexivity of the endpoint-gluing relation. -/
theorem vertexRel_refl : ∀ x, VertexRel P x x := by
  sorry

/-- Symmetry of the endpoint-gluing relation. -/
theorem vertexRel_symm : ∀ ⦃x y⦄, VertexRel P x y → VertexRel P y x := by
  sorry

/--
Transitivity uses `start ≠ finish`, which follows from the assumed nonemptiness of the edge order.
-/
theorem vertexRel_trans : ∀ ⦃x y z⦄, VertexRel P x y → VertexRel P y z → VertexRel P x z := by
  sorry

theorem vertexRel_equivalence : Equivalence (VertexRel P) where
  refl := vertexRel_refl P
  symm h := vertexRel_symm P h
  trans h h' := vertexRel_trans P h h'

def vertexSetoid : Setoid (OrderedPseudoLine.Vertex P) := ⟨VertexRel P, vertexRel_equivalence P⟩

/-- Identify only the start and finish points of `L(P)`. -/
def PointRel (x y : OrderedPseudoLine.Point P) : Prop := x = y ∨
  (x = .inl (OrderedPseudoLine.start P) ∧ y = .inl (OrderedPseudoLine.finish P)) ∨
  (x = .inl (OrderedPseudoLine.finish P) ∧ y = .inl (OrderedPseudoLine.start P))

/-- The point relation is reflexive. -/
theorem pointRel_refl : ∀ x, PointRel P x x := by
  sorry

/-- The point relation is symmetric. -/
theorem pointRel_symm : ∀ ⦃x y⦄, PointRel P x y → PointRel P y x := by
  sorry

/-- The only non-singleton point class consists of the two endpoint vertices. -/
theorem pointRel_trans : ∀ ⦃x y z⦄, PointRel P x y → PointRel P y z → PointRel P x z := by
  sorry

theorem pointRel_equivalence : Equivalence (PointRel P) where
  refl := pointRel_refl P
  symm h := pointRel_symm P h
  trans h h' := pointRel_trans P h h'

def pointSetoid : Setoid (OrderedPseudoLine.Point P) := ⟨PointRel P, pointRel_equivalence P⟩

/-- The underlying point space of the canonical pseudo-circle. -/
abbrev Point := Quotient (pointSetoid P)

/-- Its vertices are the same endpoint quotient applied to the initial segments. -/
abbrev Vertex := Quotient (vertexSetoid P)

omit [Nonempty P] in
theorem vertexRel_implies_pointRel {x y : OrderedPseudoLine.Vertex P} (h : VertexRel P x y) :
    PointRel P (.inl x) (.inl y) := by
  rcases h with h | h | h
  · exact Or.inl (congrArg Sum.inl h)
  · exact Or.inr (Or.inl ⟨congrArg Sum.inl h.1, congrArg Sum.inl h.2⟩)
  · exact Or.inr (Or.inr ⟨congrArg Sum.inl h.1, congrArg Sum.inl h.2⟩)

/-- Inclusion of quotient vertices into the quotient point space. -/
def vertexToPoint : Vertex P → Point P := Quotient.lift
    (fun v => Quotient.mk' (s := pointSetoid P) (Sum.inl v))
    (fun _ _ h => Quotient.sound (vertexRel_implies_pointRel P h))

/--
Equality of images of quotient vertices reflects `VertexRel`; no interior point participates in
the endpoint identification.
-/
theorem vertexToPoint_eq_iff (x y : OrderedPseudoLine.Vertex P) :
    vertexToPoint P (Quotient.mk' (s := vertexSetoid P) x) =
        vertexToPoint P (Quotient.mk' (s := vertexSetoid P) y) ↔
      VertexRel P x y := by
  sorry

theorem vertexToPoint_injective : Injective (vertexToPoint P) := by
  sorry

def source (p : P) : Vertex P := Quotient.mk' (s := vertexSetoid P) (OrderedPseudoLine.before P p)

def target (p : P) : Vertex P := Quotient.mk' (s := vertexSetoid P) (OrderedPseudoLine.through P p)

/-- Edge parametrization after gluing the two endvertices of the pseudo-line. -/
noncomputable def edgeParam (p : P) (t : I) : Point P :=
  Quotient.mk' (s := pointSetoid P) (OrderedPseudoLine.edgeParam P p t)

@[simp] theorem edgeParam_zero (p : P) : edgeParam P p 0 = vertexToPoint P (source P p) := by
  change Quotient.mk' (s := pointSetoid P) (OrderedPseudoLine.edgeParam P p 0) =
    Quotient.mk' (s := pointSetoid P)
      (Sum.inl (OrderedPseudoLine.before P p) : OrderedPseudoLine.Point P)
  rw [OrderedPseudoLine.edgeParam_zero]

@[simp] theorem edgeParam_one (p : P) :
    edgeParam P p 1 = vertexToPoint P (target P p) := by
  change Quotient.mk' (s := pointSetoid P) (OrderedPseudoLine.edgeParam P p 1) =
    Quotient.mk' (s := pointSetoid P)
      (Sum.inl (OrderedPseudoLine.through P p) : OrderedPseudoLine.Point P)
  rw [OrderedPseudoLine.edgeParam_one]

theorem continuous_edgeParam (p : P) : Continuous (edgeParam P p) :=
  continuous_quotient_mk'.comp (OrderedPseudoLine.continuous_edgeParam P p)

/--
The endpoint quotient is injective on every open edge, and its image there remains open in the
quotient topology because the open edge is saturated.
-/
theorem edgeInterior_openEmbedding (p : P) : IsOpenEmbedding
      (fun t : OpenUnitInterval => edgeParam P p (openToUnitInterval t)) := by
  sorry

/-- Endpoint gluing does not identify interiors of two distinct edges. -/
theorem edgeInteriors_disjoint ⦃p q : P⦄ (hpq : p ≠ q) : Disjoint
      (range (fun t : OpenUnitInterval => edgeParam P p (openToUnitInterval t)))
      (range (fun t : OpenUnitInterval => edgeParam P q (openToUnitInterval t))) := by
  sorry

/-- Quotient vertices remain disjoint from all open edge interiors. -/
theorem vertices_disjoint_edgeInteriors (p : P) : Disjoint (range (vertexToPoint P))
      (range (fun t : OpenUnitInterval => edgeParam P p (openToUnitInterval t))) := by
  sorry

/-- The quotient of the pseudo-line cover is the vertex/open-edge cover of the pseudo-circle. -/
theorem vertex_or_edgeInterior_covers : range (vertexToPoint P) ∪
      ⋃ p, range (fun t : OpenUnitInterval => edgeParam P p (openToUnitInterval t)) = univ := by
  sorry

/--
A separation of two quotient vertices can be chosen on the pseudo-line so that start and finish
lie on the same side; it therefore descends through the endpoint quotient.
-/
theorem exists_open_vertexBipartition
    ⦃v w : Vertex P⦄ (hvw : v ≠ w) : ∃ Q : IndexedVertexPartition (Vertex P) Bool,
      IsOpenRealizableVertexPartition (Point := TopCat.of (Point P))
        (⟨vertexToPoint P, vertexToPoint_injective P⟩ : Vertex P ↪ Point P) Q ∧
      Q.Separates v w := by
  sorry

/--
The canonical pseudo-circle obtained from the nontrivial pseudo-line `L(P)` by identifying its
endvertices.  Its edge type is definitionally `P`; its point topology is the quotient topology.
-/
noncomputable def space : GraphLikeSpace.{u,u,u} where
  Point := TopCat.of (Point P)
  Vertex := Vertex P
  Edge := P
  vertex := ⟨vertexToPoint P, vertexToPoint_injective P⟩
  source := source P
  target := target P
  edgePath p :=
    { toFun := edgeParam P p
      source' := edgeParam_zero P p
      target' := edgeParam_one P p
      continuous_toFun := continuous_edgeParam P p }
  edgeInterior_openEmbedding := edgeInterior_openEmbedding P
  edgeInteriors_disjoint := fun _ _ h => edgeInteriors_disjoint P h
  vertices_disjoint_edgeInteriors := vertices_disjoint_edgeInteriors P
  point_eq_vertex_or_edgeInterior := vertex_or_edgeInterior_covers P
  separate_vertices := exists_open_vertexBipartition P

theorem pointSpace_is_endpointQuotient : Nonempty ((space P).Point ≃ₜ Point P) := by
  exact ⟨Homeomorph.refl _⟩

/-- The quotient projection from the compact pseudo-line is continuous and surjective. -/
theorem quotientMap_isQuotient : IsQuotientMap
      (Quotient.mk' (s := pointSetoid P) : OrderedPseudoLine.Point P → Point P) := by
  sorry

/-- Compactness descends along the continuous surjective endpoint quotient. -/
theorem pointSpace_compact : _root_.IsCompact (univ : Set (Point P)) := by
  sorry

theorem space_compact : (space P).IsCompact := by
  exact pointSpace_compact P

/-- Connectedness also descends along the endpoint quotient. -/
theorem space_connected : IsConnected (univ : Set (space P).Point) := by
  sorry

end OrderedPseudoCircle

namespace GraphLikeSpace

variable (X : GraphLikeSpace.{u,u,u})

/--
Topological circuits are edge sets of injective graph-like maps from canonical pseudo-circles.
The total order is allowed to be uncountable; countable pseudo-circles reduce later to ordinary
copies of `S¹`.
-/
def IsTopologicalCircuit (C : Set X.Edge) : Prop :=
  ∃ (P : Type u) (order : LinearOrder P) (nonempty : Nonempty P),
    letI := order
    letI := nonempty
    ∃ φ : Embedding (OrderedPseudoCircle.space P) X, range φ.edgeEmbedding = C

/--
`X` induces `M` when topological circuits and bonds are exactly the circuits and cocircuits of
`M`.  Not every graph-like space induces a matroid, so this must remain a predicate.
-/
def Induces (M : Matroid X.Edge) : Prop := M.E = univ ∧
  (∀ C, M.IsCircuit C ↔ X.IsTopologicalCircuit C) ∧ (∀ B, M.IsCocircuit B ↔ X.IsTopologicalBond B)

/--
Deleting the interior of one edge from a canonical pseudo-circle leaves the corresponding
closed pseudo-arc and is connected.
-/
theorem OrderedPseudoCircle.complement_edgeInterior_connected {P : Type u} [LinearOrder P]
  [Nonempty P] (e : P) :
    IsConnected
      (univ \ (OrderedPseudoCircle.space P).edgeInterior e :
        Set (OrderedPseudoCircle.space P).Point) := by
  sorry

/--
A topological cut of a pseudo-circle cannot consist of one edge.  Otherwise the two open sides
would disconnect the connected pseudo-arc left after removing that edge.
-/
theorem OrderedPseudoCircle.topologicalCut_encard_ne_one {P : Type u} [LinearOrder P] [Nonempty P]
    {B : Set (OrderedPseudoCircle.space P).Edge}
    (hB : (OrderedPseudoCircle.space P).IsTopologicalCut B) : B.encard ≠ 1 := by
  sorry

/--
Compact-open-cover lemma (BCC Lemma 4.21) specialized to a pseudo-circle.  Cover the
pseudo-circle by the two open sides of the cut and by its open edge interiors.  A finite
subcover shows that only finitely many circle edges can cross between the sides.
-/
theorem Embedding.pseudoCircle_range_inter_cut_finite {P : Type u} [LinearOrder P] [Nonempty P]
    (φ : Embedding (OrderedPseudoCircle.space P) X) {B : Set X.Edge} (hB : X.IsTopologicalCut B) :
    (range φ.edgeEmbedding ∩ B).Finite := by
  sorry

/--
The same compact-open-cover argument with the whole compact graph-like space in place of a
pseudo-circle shows that every topological cut is finite.
-/
theorem topologicalCut_finite_of_compact (hX : X.IsCompact) {B : Set X.Edge}
    (hB : X.IsTopologicalCut B) : B.Finite := by
  sorry

/-- In particular, every bond of a compact graph-like space is finite. -/
theorem topologicalBond_finite_of_compact (hX : X.IsCompact) {B : Set X.Edge}
    (hB : X.IsTopologicalBond B) : B.Finite := by
  exact X.topologicalCut_finite_of_compact hX hB.prop.2

/--
Pull an ambient-open vertex bipartition back along a graph-like embedding.  Its edge boundary is
the inverse image of the original edge boundary under the stored edge embedding.
-/
theorem Embedding.exists_pullback_vertexBipartition {Z X : GraphLikeSpace.{u,u,u}}
    (φ : Embedding Z X) (P : X.VertexBipartition) (hP : VertexPartition.HasOpenRealization P) :
    ∃ Q : Z.VertexBipartition, VertexPartition.HasOpenRealization Q ∧
      ∀ e, e ∈ Q.edgeBoundary ↔ φ.edgeEmbedding e ∈ P.edgeBoundary := by
  sorry

/--
Consequently, an embedded pseudo-circle cannot meet a topological cut in exactly one of its
image edges.
-/
theorem Embedding.pseudoCircle_range_inter_cut_encard_ne_one {P : Type u} [LinearOrder P]
    [Nonempty P] (φ : Embedding (OrderedPseudoCircle.space P) X) {B : Set X.Edge}
    (hB : X.IsTopologicalCut B) : (range φ.edgeEmbedding ∩ B).encard ≠ 1 := by
  sorry

/-- A topological circuit meets every topological cut in only finitely many edges. -/
theorem topologicalCircuit_inter_topologicalCut_finite {C B : Set X.Edge}
    (hC : X.IsTopologicalCircuit C) (hB : X.IsTopologicalCut B) : (C ∩ B).Finite := by
  rcases hC with ⟨P, horder, hnonempty, φ, hφ⟩
  letI := horder
  letI := hnonempty
  rw [← hφ]
  exact Embedding.pseudoCircle_range_inter_cut_finite (X := X) φ hB

theorem topologicalCircuit_inter_topologicalCut_ne_singleton {C B : Set X.Edge}
    (hC : X.IsTopologicalCircuit C) (hB : X.IsTopologicalCut B) : (C ∩ B).encard ≠ 1 := by
  rcases hC with ⟨P, horder, hnonempty, φ, hφ⟩
  letI := horder
  letI := hnonempty
  rw [← hφ]
  exact Embedding.pseudoCircle_range_inter_cut_encard_ne_one (X := X) φ hB

end GraphLikeSpace

/-! ## 3. Ordinary graphs and the two realization topologies -/

namespace Realization

variable {α : Type u} {β : Type v} (G : Graph α β)

abbrev Vertices := {v : α // v ∈ G.vertexSet}
abbrev Edges := {e : β // e ∈ G.edgeSet}

/-- An explicit name for the CW/quotient topology, independent of inferred metric instances. -/
@[instance_reducible]
noncomputable def quotientTopology : TopologicalSpace G.Realization := TopologicalSpace.coinduced
    (Quotient.mk' (s := G.glueRel) : G.PreRealization → G.Realization)
    (inferInstance : TopologicalSpace G.PreRealization)

/-- A tag for the realization carrying the quotient (weak CW) topology. -/
def Weak := G.Realization

/-- A tag for the same carrier carrying the unit-edge path extended metric. -/
def Metric := G.Realization

noncomputable instance : TopologicalSpace (Weak G) :=
  quotientTopology G

noncomputable instance : EMetricSpace (Metric G) :=
  Graph.Realization.eMetricSpace G

/-- The carrier identity from the weak realization to the metric realization. -/
def weakToMetric (x : Weak G) : Metric G := x

/-- The carrier identity from the metric realization to the weak realization. -/
def metricToWeak (x : Metric G) : Weak G := x

/-- The quotient map from the pre-realization into the weakly topologized realization. -/
def preToWeak (x : G.PreRealization) : Weak G := Quotient.mk' (s := G.glueRel) x

/-- The same quotient map, with the metric topology placed on its codomain. -/
def preToMetric (x : G.PreRealization) : Metric G := Quotient.mk' (s := G.glueRel) x

/-- The two tags are equivalent before topology is considered. -/
def carrierEquiv : Weak G ≃ Metric G := Equiv.refl _

/-- The pre-realization quotient map is a quotient map onto the weak realization. -/
theorem preToWeak_isQuotientMap : IsQuotientMap (preToWeak G) := by
  sorry

/--
On each summand of `PreRealization` the map to the unit-edge path metric is continuous: it is
constant on vertex summands and the standard unit parametrization on edge summands.
-/
theorem continuous_preToMetric : Continuous (preToMetric G) := by
  sorry

/-- The metric quotient map factors through the weak quotient map by carrier identity. -/
theorem preToMetric_eq_weakToMetric_comp : preToMetric G = weakToMetric G ∘ preToWeak G := by
  rfl

/-- The weak topology is finer than the fixed unit-edge metric topology. -/
theorem continuous_weakToMetric : Continuous (weakToMetric G) := by
  sorry

/--
Local finiteness supplies the missing uniformity at vertices: every weak neighbourhood contains
a metric ball.  At an edge-interior point this follows from the ordinary interval topology; at a
vertex only finitely many incident edge germs need be controlled.
-/
theorem weak_open_contains_metric_ball [G.LocallyFinite] {U : Set (Weak G)} (hU : IsOpen U)
    {x : Weak G} (hx : x ∈ U) : ∃ ε : ENNReal, 0 < ε ∧
      Metric.eball (weakToMetric G x) ε ⊆ weakToMetric G '' U := by
  sorry

/-- The metric-to-weak carrier identity is continuous under local finiteness. -/
theorem continuous_metricToWeak_of_locallyFinite [G.LocallyFinite] :
    Continuous (metricToWeak G) := by
  sorry

/--
For locally finite graphs the weak CW topology and the unit-edge metric topology agree.
This is the precise place where local finiteness belongs.
-/
theorem locallyFinite_isHomeomorph [G.LocallyFinite] : IsHomeomorph (weakToMetric G) := by
  sorry

/-- The Euclidean plane used by drawing statements. -/
abbrev Plane := EuclideanSpace ℝ (Fin 2)

/--
A strict realization drawing.  This is the quotient-topology formulation of compatible
vertex/edge curves with no identifications other than the prescribed endpoint gluings.
-/
structure Drawing where
  toFun : Weak G → Plane
  continuous_toFun : Continuous toFun
  injective_toFun : Injective toFun

def IsDrawablePlanar : Prop := Nonempty (Drawing G)

/-- Topological planarity of the fixed unit-edge metric realization. -/
def IsMetricPlanar : Prop := ∃ f : Metric G → Plane, IsEmbedding f

/-- A metric embedding is automatically a weak drawing because `weakToMetric` is continuous. -/
theorem drawablePlanar_of_metricPlanar : IsMetricPlanar G → IsDrawablePlanar G := by
  sorry

/-- A countable vertex-and-edge carrier admits an increasing finite exhaustion. -/
theorem exists_finite_cell_exhaustion [Countable (Vertices G)] [Countable (Edges G)] :
    ∃ K : ℕ → Finset (Vertices G ⊕ Edges G), Monotone K ∧ ∀ x, ∃ n, x ∈ K n := by
  sorry

/--
Untelescoping lemma.  Starting from a strict weak drawing and a finite cell exhaustion, construct
successively protected vertex disks and edge tubes.  At stage `n`, redraw the next finite batch
inside those tubes with a fixed positive collar.  The collars make the limiting map continuous
for the unit-edge metric at every infinite-degree vertex; nested protection gives injectivity and
continuity of the inverse onto the image.
-/
theorem Drawing.exists_metricEmbedding_of_countable [Countable (Vertices G)] [Countable (Edges G)]
    (D : Drawing G) : ∃ f : Metric G → Plane, IsEmbedding f := by
  sorry

/--
The fixed metric formulation is not equivalent for arbitrary cardinality.  Countability is the
proposed theorem boundary; in particular, an uncountable star is weakly drawable but its unit
hedgehog metric cannot embed in the second-countable plane.
-/
theorem drawablePlanar_iff_metricPlanar [Countable (Vertices G)] [Countable (Edges G)] :
    IsDrawablePlanar G ↔ IsMetricPlanar G := by
  constructor
  · rintro ⟨D⟩
    exact D.exists_metricEmbedding_of_countable
  · exact drawablePlanar_of_metricPlanar G

/-- Incidence data saying that `X` is a topological presentation of the ordinary graph `G`. -/
structure PresentsGraph (X : GraphLikeSpace.{w,u,v}) where
  vertexEquiv : X.Vertex ≃ Vertices G
  edgeEquiv : X.Edge ≃ Edges G
  incidence_iff : ∀ e v w, G.IsLink (edgeEquiv e).1 (vertexEquiv v).1 (vertexEquiv w).1 ↔
      s(v, w) = s(X.source e, X.target e)

/--
The quotient classes of graph vertices are distinct, each open edge cell maps homeomorphically
onto an open subset, different cells are disjoint, and the cells together with the vertices cover
the weak realization.
-/
theorem weak_quotient_has_graphLike_cell_decomposition : ∃ X : GraphLikeSpace.{max u v, u, v},
      Nonempty (X.Point ≃ₜ Weak G) ∧ Nonempty (X.Vertex ≃ Vertices G) ∧
      Nonempty (X.Edge ≃ Edges G) := by
  sorry

/--
Choosing an orientation of every active edge identifies the endpoints of the graph-like cell
decomposition with the two endpoints recorded by `G.IsLink`.
-/
theorem weak_cell_decomposition_presents_incidence (X : GraphLikeSpace.{max u v, u, v})
    (hX : Nonempty (X.Point ≃ₜ Weak G)) (hV : Nonempty (X.Vertex ≃ Vertices G))
    (hE : Nonempty (X.Edge ≃ Edges G)) : ∃ X' : GraphLikeSpace.{max u v, u, v},
      Nonempty (X'.Point ≃ₜ Weak G) ∧ Nonempty (PresentsGraph G X') := by
  sorry

/-- Milestone: the quotient realization of an ordinary graph has canonical graph-like structure. -/
theorem weak_realization_has_graphLikeStructure : ∃ X : GraphLikeSpace.{max u v, u, v},
      Nonempty (X.Point ≃ₜ Weak G) ∧ Nonempty (PresentsGraph G X) := by
  rcases weak_quotient_has_graphLike_cell_decomposition G with ⟨X, hX, hV, hE⟩
  exact weak_cell_decomposition_presents_incidence G X hX hV hE

end Realization

namespace GraphLikeSpace

variable (X : GraphLikeSpace.{u,v,w})

/--
The graph-like separation axiom, together with the open interval charts, separates any two
points; hence every graph-like space is Hausdorff.
-/
theorem point_t2Space : T2Space X.Point := by
  sorry

/--
For finite vertex and edge sets, the point space is a finite union of compact vertex singletons
and compact closed-edge images.
-/
theorem finite_pointSpace_compact [Finite X.Vertex] [Finite X.Edge] : X.IsCompact := by
  sorry

/--
Map the weak realization of the incidence graph to `X` by sending vertices through `X.vertex`
and each unit interval through its stored edge path.  Endpoint compatibility makes the map
descend through the realization quotient.
-/
theorem exists_continuous_incidenceRealizationMap [Finite X.Vertex] [Finite X.Edge] :
    ∃ f : Realization.Weak X.incidenceGraph → X.Point, Continuous f ∧ Surjective f ∧
      ∀ (e : X.incidenceGraph.edgeSet) t, f (Quotient.mk' (s := X.incidenceGraph.glueRel)
          (Sum.inr ⟨e, openToUnitInterval t⟩)) = X.edgePath e.1 (openToUnitInterval t) := by
  sorry

/--
The descended map is injective: open edge interiors are mutually disjoint and disjoint from
vertices, while the finite graph-like topology leaves no additional point identifications.
-/
theorem incidenceRealizationMap_injective [Finite X.Vertex] [Finite X.Edge]
    {f : Realization.Weak X.incidenceGraph → X.Point} (hf : Continuous f) (hsurj : Surjective f)
    (hcell : ∀ (e : X.incidenceGraph.edgeSet) t, f (Quotient.mk' (s := X.incidenceGraph.glueRel)
        (Sum.inr ⟨e, openToUnitInterval t⟩)) = X.edgePath e.1 (openToUnitInterval t)) :
    Injective f := by
  sorry

/--
Compact-to-Hausdorff upgrades the canonical continuous bijection to a homeomorphism.  The
homeomorphism is stated in the opposite direction to the canonical map.
-/
theorem incidenceRealizationMap_homeomorph_of_bijective [Finite X.Vertex] [Finite X.Edge]
    {f : Realization.Weak X.incidenceGraph → X.Point} (hf : Continuous f) (hsurj : Surjective f)
    (hinj : Injective f) : Nonempty (X.Point ≃ₜ Realization.Weak X.incidenceGraph) := by
  sorry

/--
Select the canonical cellwise map, prove its injectivity from the exact edge formula, and apply
the compact-to-Hausdorff upgrade.  This is the topological final step after the quotient and cell
calculations.
-/
theorem finite_incidenceRealization_homeomorph [Finite X.Vertex] [Finite X.Edge] : Nonempty
      (X.Point ≃ₜ Realization.Weak X.incidenceGraph) := by
  rcases X.exists_continuous_incidenceRealizationMap with
    ⟨f, hf, hsurj, hcell⟩
  apply X.incidenceRealizationMap_homeomorph_of_bijective hf hsurj
  exact X.incidenceRealizationMap_injective hf hsurj hcell

/--
Bowler--Carmesin--Christian Lemma 3.2: with finitely many vertices and edges, no extra
point-set topology remains; the space is the weak realization of its abstract incidence graph.
-/
theorem finite_homeomorphic_incidenceRealization [Finite X.Vertex] [Finite X.Edge] : Nonempty
      (X.Point ≃ₜ Realization.Weak X.incidenceGraph) := by
  exact X.finite_incidenceRealization_homeomorph

end GraphLikeSpace

/-! ## 4. Faces and geometric duals -/

namespace Geometric

variable (X : GraphLikeSpace.{u,u,u}) (S : TopCat.{u})

/-- A topological embedding of the whole graph-like point space. -/
structure Embedding where
  toFun : X.Point → S
  isEmbedding : IsEmbedding toFun

namespace Embedding

variable {X S} (φ : Embedding X S)

instance : FunLike (Embedding X S) X.Point S where
  coe := Embedding.toFun
  coe_injective φ ψ h := by
    cases φ
    cases ψ
    simp_all

/-- Faces are connected components of the complement of the embedded image. -/
abbrev Faces := ConnectedComponents {x : S // x ∉ range φ.toFun}

/-- The subset of the ambient space represented by a face. -/
def faceSet (F : φ.Faces) : Set S := Subtype.val '' ConnectedComponents.mk ⁻¹' {F}

/-- A face is incident with an edge when the whole open edge lies in its closure. -/
def FaceAdherentToEdge (F : φ.Faces) (e : X.Edge) : Prop := range (fun t : OpenUnitInterval =>
    φ (X.edgePath e (openToUnitInterval t))) ⊆ closure (φ.faceSet F)

/--
The two local sides of every embedded edge.  `Sym2` is essential: a bridge can have the same face
on both sides.  The compatibility field rules out silently choosing arbitrary faces.
-/
structure EdgeSides where
  sides : X.Edge → Sym2 φ.Faces
  mem_sides_iff : ∀ e F, F ∈ sides e ↔ φ.FaceAdherentToEdge F e

/-- The abstract face-dual graph determined by side data. -/
def faceDualGraph (D : φ.EdgeSides) : Graph φ.Faces X.Edge where
  vertexSet := univ
  edgeSet := univ
  IsLink e F K := D.sides e = s(F, K)
  isLink_symm := by
    intro e _
    exact ⟨fun F K h => by simpa only [Sym2.eq_swap] using h⟩
  eq_or_eq_of_isLink_of_isLink := by
    intro e F K F' K' h h'
    have heq := Sym2.eq_iff.mp (h.symm.trans h')
    exact heq.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  edge_mem_iff_exists_isLink := by
    intro e
    simp only [mem_univ, true_iff]
    induction D.sides e using Sym2.ind with
    | _ F K => exact ⟨F, K, rfl⟩
  left_mem_of_isLink := by simp

end Embedding

/-- An open topological disk. -/
def IsOpenDisk {T : TopCat.{u}} (U : Set T) : Prop := Nonempty (U ≃ₜ Metric.ball (0 : ℂ) 1)

/-- A boundaryless topological surface, stated without committing to a smooth structure. -/
def IsTopologicalSurface (S : TopCat.{u}) : Prop := T2Space S ∧ SecondCountableTopology S ∧
    ∀ x : S, ∃ U : Set S, IsOpen U ∧ x ∈ U ∧ IsOpenDisk U

/-- A fixed topological model of the circle. -/
abbrev UnitCircle := (Metric.sphere (0 : ℂ) 1 : Set ℂ)

/-- A subset is a simple closed curve when it is the image of an embedded circle. -/
def IsSimpleClosedCurve {T : TopCat.{u}} (K : Set T) : Prop :=
  ∃ γ : UnitCircle → T, IsEmbedding γ ∧ range γ = K

/-- A set separates its ambient space when its complement is disconnected. -/
def Separates {T : TopCat.{u}} (K : Set T) : Prop := ¬ IsPreconnected (univ : Set {x : T // x ∉ K})

/--
Allowed planar input 1: the weak Jordan curve theorem.  The complement of a simple closed curve
in the plane has exactly two connected components.
-/
theorem jordanCurve_two_regions {K : Set Realization.Plane}
    (hK : IsSimpleClosedCurve (T := TopCat.of Realization.Plane) K) : Nonempty
      (ConnectedComponents {x : Realization.Plane // x ∉ K} ≃ Bool) := by
  sorry

/--
Allowed planar input 2: the partial converse.  A compact planar separator contains a simple
closed curve.
-/
theorem compact_separator_contains_jordanCurve {K : Set Realization.Plane}
    (hKc : _root_.IsCompact K) (hKsep : Separates (T := TopCat.of Realization.Plane) K) :
    ∃ J : Set Realization.Plane, J ⊆ K ∧
      IsSimpleClosedCurve (T := TopCat.of Realization.Plane) J := by
  sorry

/-- A cellular embedding has an open-disk complement component at every face. -/
def Embedding.IsCellular {X : GraphLikeSpace.{u,u,u}} {S : TopCat.{u}} (φ : Embedding X S) : Prop :=
  ∀ F : φ.Faces, IsOpenDisk (φ.faceSet F)

/-- A compact embedded graph-like space has closed image in a Hausdorff surface. -/
theorem Embedding.isClosed_range {X : GraphLikeSpace.{u,u,u}} {S : TopCat.{u}} (φ : Embedding X S)
    (hS : IsTopologicalSurface S) (hX : X.IsCompact) : IsClosed (range φ.toFun) := by
  sorry

/--
An interior point of an edge has an ambient neighbourhood whose intersection with the whole
drawing is just an open subarc of that edge.  Use openness of the edge interior in `X`, the
homeomorphism onto the image, and closedness of the compact image.
-/
theorem Embedding.exists_isolating_edgeNeighbourhood {X : GraphLikeSpace.{u,u,u}} {S : TopCat.{u}}
    (φ : Embedding X S) (hS : IsTopologicalSurface S) (hX : X.IsCompact) (e : X.Edge)
    (t : OpenUnitInterval) : ∃ U : Set S, IsOpen U ∧ φ (X.edgePath e (openToUnitInterval t)) ∈ U ∧
      U ∩ range φ.toFun = U ∩ range (fun s : OpenUnitInterval =>
          φ (X.edgePath e (openToUnitInterval s))) := by
  sorry

/--
Local crosscut lemma derived from the two allowed planar principles: an isolated embedded open
arc in a surface chart has exactly two complementary side germs.  Close a smaller subarc outside
the chart to a simple closed curve and apply `jordanCurve_two_regions`.
-/
theorem Embedding.edgePoint_has_two_complement_germs {X : GraphLikeSpace.{u,u,u}} {S : TopCat.{u}}
    (φ : Embedding X S) (hS : IsTopologicalSurface S) (hX : X.IsCompact) (e : X.Edge)
    (t : OpenUnitInterval) : ∃ F K : φ.Faces,
      F ∈ {L | φ.FaceAdherentToEdge L e} ∧ K ∈ {L | φ.FaceAdherentToEdge L e} := by
  sorry

/--
Side germs propagate along the connected parameter interval.  The unordered pair cannot change
without producing a third local complement germ at a first transition point.
-/
theorem Embedding.edge_adherent_faces_independent_of_parameter {X : GraphLikeSpace.{u,u,u}}
    {S : TopCat.{u}} (φ : Embedding X S) (hS : IsTopologicalSurface S) (hX : X.IsCompact)
    (e : X.Edge) : ∃ F K : φ.Faces, ∀ L, φ.FaceAdherentToEdge L e ↔ L = F ∨ L = K := by
  sorry

/-- Package the preceding unordered face pair for every edge as `EdgeSides`. -/
theorem Embedding.edgeSides_of_adherent_face_pairs {X : GraphLikeSpace.{u,u,u}} {S : TopCat.{u}}
    (φ : Embedding X S) (hpair : ∀ e : X.Edge, ∃ F K : φ.Faces,
      ∀ L, φ.FaceAdherentToEdge L e ↔ L = F ∨ L = K) :
    Nonempty φ.EdgeSides := by
  sorry

/-- An embedded graph-like space in a surface has two (not necessarily distinct) face sides. -/
theorem Embedding.exists_edgeSides_of_surface {X : GraphLikeSpace.{u,u,u}} {S : TopCat.{u}}
    (φ : Embedding X S) (hS : IsTopologicalSurface S) (hX : X.IsCompact) :
    Nonempty φ.EdgeSides := by
  apply φ.edgeSides_of_adherent_face_pairs
  exact fun e => φ.edge_adherent_faces_independent_of_parameter hS hX e

/-- The open square used in the local definition of a transverse crossing. -/
abbrev OpenSquare := Set.Ioo (-1 : ℝ) 1 × Set.Ioo (-1 : ℝ) 1

def openSquareOrigin : OpenSquare := (⟨0, by norm_num⟩, ⟨0, by norm_num⟩)

def horizontalAxis : Set OpenSquare := {p | (p.2 : ℝ) = 0}
def verticalAxis : Set OpenSquare := {p | (p.1 : ℝ) = 0}

/--
Two subsets cross topologically at `p` when a neighbourhood chart sends their complete local
traces to the two coordinate axes.  This excludes tangencies and extra branches at the crossing.
-/
def IsTopologicalCrossingAt {S : TopCat.{u}} (A B : Set S) (p : S) : Prop :=
  ∃ (U : Set S) (hp : p ∈ U) (h : U ≃ₜ OpenSquare), IsOpen U ∧ h ⟨p, hp⟩ = openSquareOrigin ∧
    h '' {x : U | (x : S) ∈ A} = horizontalAxis ∧ h '' {x : U | (x : S) ∈ B} = verticalAxis

variable {X : GraphLikeSpace.{u,u,u}} {Y : GraphLikeSpace.{u,u,u}} {S : TopCat.{u}}

/--
A geometric dual pair before cellularity is imposed.

The exact-intersection axiom says that corresponding edges cross once in their interiors and
there are no other primal--dual intersections.
-/
structure DualPair where
  primal : Embedding X S
  dual : Embedding Y S
  edgeEquiv : X.Edge ≃ Y.Edge
  primalCrossingParameter : X.Edge → OpenUnitInterval
  dualCrossingParameter : X.Edge → OpenUnitInterval
  intersection_iff : ∀ x y, primal x = dual y ↔ ∃ e : X.Edge,
      x = X.edgePath e (openToUnitInterval (primalCrossingParameter e)) ∧
      y = Y.edgePath (edgeEquiv e) (openToUnitInterval (dualCrossingParameter e))
  transverse : ∀ e, IsTopologicalCrossingAt (range primal.toFun) (range dual.toFun)
    (primal (X.edgePath e (openToUnitInterval (primalCrossingParameter e))))

/--
A face dual pair, without assuming that either embedding is cellular.  Each face--vertex
equivalence records both incidence with edge sides and the geometric fact that the paired
opposite vertex lies in that face.  The latter is essential: endpoint compatibility alone permits
an arbitrary permutation among faces having the same boundary data, and is too weak for
pseudosurface defect duality.
-/
structure FaceDualPair : Type u extends DualPair (X := X) (Y := Y) (S := S) where
  primalSides : toDualPair.primal.EdgeSides
  dualSides : toDualPair.dual.EdgeSides
  primalFaceToDualVertex : toDualPair.primal.Faces ≃ Y.Vertex
  dualFaceToPrimalVertex : toDualPair.dual.Faces ≃ X.Vertex
  dualVertex_mem_primalFace_iff : ∀ F v,
    toDualPair.dual (Y.vertex v) ∈ toDualPair.primal.faceSet F ↔ v = primalFaceToDualVertex F
  primalVertex_mem_dualFace_iff : ∀ F v,
    toDualPair.primal (X.vertex v) ∈ toDualPair.dual.faceSet F ↔ v = dualFaceToPrimalVertex F
  primalSide_endpoint_compatibility : ∀ e, Sym2.map primalFaceToDualVertex (primalSides.sides e) =
      s(Y.source (toDualPair.edgeEquiv e), Y.target (toDualPair.edgeEquiv e))
  dualSide_endpoint_compatibility : ∀ e, Sym2.map dualFaceToPrimalVertex
      (dualSides.sides (toDualPair.edgeEquiv e)) = s(X.source e, X.target e)

/-- A face dual pair for which both complementary decompositions consist of open disks. -/
structure CellularDualPair : Type u extends FaceDualPair (X := X) (Y := Y) (S := S) where
  primalCellular : toFaceDualPair.toDualPair.primal.IsCellular
  dualCellular : toFaceDualPair.toDualPair.dual.IsCellular

/--
A dual pair is matroidal when its specified edge equivalence exchanges topological circuits and
bonds.  Mentioning `D.edgeEquiv` here is important: mere existence of some abstract isomorphism
would not say that the geometrically crossing edges are the dual elements.
-/
def DualPair.IsMatroidal (D : DualPair (X := X) (Y := Y) (S := S)) : Prop :=
  ∀ M : Matroid X.Edge, X.Induces M → (∀ C : Set X.Edge,
      M.IsCocircuit C ↔ Y.IsTopologicalCircuit (D.edgeEquiv '' C)) ∧
    (∀ C : Set X.Edge, M.IsCircuit C ↔ Y.IsTopologicalBond (D.edgeEquiv '' C))

/-- The topological two-sphere, up to homeomorphism. -/
def IsTopologicalTwoSphere (S : TopCat.{u}) : Prop := Nonempty
    (S ≃ₜ (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 : Set (EuclideanSpace ℝ (Fin 3))))

/-- A space homeomorphic to the two-sphere is a topological surface. -/
theorem IsTopologicalTwoSphere.isTopologicalSurface (hS : IsTopologicalTwoSphere S) :
    IsTopologicalSurface S := by
  sorry

/--
The planar Jordan theorem transfers to a two-sphere by choosing a point off the compact curve and
using stereographic projection.
-/
theorem jordanCurve_two_regions_of_twoSphere (hS : IsTopologicalTwoSphere S) {K : Set S}
    (hK : IsSimpleClosedCurve (T := S) K) :
    Nonempty (ConnectedComponents {x : S // x ∉ K} ≃ Bool) := by
  sorry

/--
The partial converse transfers in the same way: first choose the puncture in one complementary
component, then apply the planar theorem to the stereographic image.
-/
theorem compact_separator_contains_jordanCurve_of_twoSphere (hS : IsTopologicalTwoSphere S)
    {K : Set S} (hKc : _root_.IsCompact K) (hKsep : Separates (T := S) K) :
    ∃ J : Set S, J ⊆ K ∧ IsSimpleClosedCurve (T := S) J := by
  sorry

/-- The image in `S` of the standard subspace supported on an edge set. -/
def Embedding.edgeSetImage (φ : Embedding X S) (A : Set X.Edge) : Set S :=
  φ.toFun '' X.standardSubspacePointSet A

/--
Radial data inside all primal faces.  Each incidence `(e,b)` has a spoke from the chosen face
centre to a chosen interior point of `e`; spoke interiors lie in their face, are mutually
disjoint, and meet the primal drawing only at their ports.
-/
structure FaceSpokeSystem (φ : Embedding X S) (A : φ.EdgeSides) where
  side : X.Edge → Bool → φ.Faces
  sides_eq : ∀ e, A.sides e = s(side e false, side e true)
  centre : φ.Faces ↪ S
  centre_mem : ∀ F, centre F ∈ φ.faceSet F
  portParameter : X.Edge → OpenUnitInterval
  spoke : (i : X.Edge × Bool) → Path (centre (side i.1 i.2))
      (φ (X.edgePath i.1 (openToUnitInterval (portParameter i.1))))
  spoke_injective : ∀ i, Injective (spoke i)
  spoke_in_face : ∀ i, range (fun t : OpenUnitInterval => spoke i (openToUnitInterval t)) ⊆
      φ.faceSet (side i.1 i.2)
  centres_disjoint_spokeInteriors : Disjoint (range centre)
      (⋃ i, range (fun t : OpenUnitInterval => spoke i (openToUnitInterval t)))
  spokeInteriors_pairwiseDisjoint : Pairwise (Disjoint on (fun i : X.Edge × Bool =>
          range (fun t : OpenUnitInterval => spoke i (openToUnitInterval t))))
  spoke_meets_primal_only_at_port : ∀ i x t, φ x = spoke i t → t
      = 1 ∧ x = X.edgePath i.1 (openToUnitInterval (portParameter i.1))

/--
Inside one open disk, choose a centre and noncrossing radial spokes to all boundary ports.  The
ports are countable because their edge interiors give pairwise-disjoint open subsets of the
second-countable surface.  Construct the spokes inductively in nested finite polygonal
approximations, using the weak Jordan theorem to keep every new spoke in the correct component.
-/
theorem Embedding.exists_faceSpokeSystem (φ : Embedding X S) (hX : X.IsCompact)
    (hS : IsTopologicalTwoSphere S) (hφ : φ.IsCellular) (A : φ.EdgeSides) :
    Nonempty (FaceSpokeSystem φ A) := by
  sorry

/--
Data for the entire dual drawing after gluing the two spokes at each primal-edge port.
-/
structure DualDrawingData (φ : Embedding X S) (A : φ.EdgeSides) where
  side₀ : X.Edge → φ.Faces
  side₁ : X.Edge → φ.Faces
  sides_eq : ∀ e, A.sides e = s(side₀ e, side₁ e)
  dualVertex : φ.Faces ↪ S
  primalCrossingParameter : X.Edge → OpenUnitInterval
  dualCrossingParameter : X.Edge → OpenUnitInterval
  dualPath : (e : X.Edge) → Path (dualVertex (side₀ e)) (dualVertex (side₁ e))
  edgeInterior_openEmbedding : ∀ e, IsOpenEmbedding
      (fun t : OpenUnitInterval => dualPath e (openToUnitInterval t))
  edgeInteriors_disjoint : ∀ ⦃e f⦄, e ≠ f → Disjoint
      (range (fun t : OpenUnitInterval => dualPath e (openToUnitInterval t)))
      (range (fun t : OpenUnitInterval => dualPath f (openToUnitInterval t)))
  vertices_disjoint_edgeInteriors : ∀ e, Disjoint (range dualVertex)
      (range (fun t : OpenUnitInterval => dualPath e (openToUnitInterval t)))
  primal_dual_intersection_iff : ∀ x e t, φ x = dualPath e t ↔ x = X.edgePath e
      (openToUnitInterval (primalCrossingParameter e)) ∧
    t = openToUnitInterval (dualCrossingParameter e)
  transverse : ∀ e, IsTopologicalCrossingAt (range φ.toFun)
    (range dualVertex ∪ ⋃ f, range (dualPath f))
    (φ (X.edgePath e (openToUnitInterval (primalCrossingParameter e))))

/-- Concatenating opposite spokes produces the exact transverse dual drawing data. -/
theorem FaceSpokeSystem.exists_dualDrawingData {φ : Embedding X S} {A : φ.EdgeSides}
    (R : FaceSpokeSystem φ A) : Nonempty (DualDrawingData φ A) := by
  sorry

/--
Give the union of dual vertices and open dual edges its subspace topology.  The spoke separation
properties verify the graph-like axioms, face/vertex compatibility, dual cellularity, and exact
intersection.

The resulting dual is deliberately **not** asserted compact.  For a compact graph-like continuum
the geometric dual is generally an infinite graph-like space; its missing accumulation points
can lie on the primal drawing.  Forcing compactness would either add unwanted dual vertices or
create extra primal--dual intersections.
-/
theorem DualDrawingData.assembles_cellularDual {φ : Embedding X S} {A : φ.EdgeSides}
    (R : DualDrawingData φ A) (hX : X.IsCompact) (hS : IsTopologicalTwoSphere S) (hφ : φ.IsCellular)
    : ∃ (Y : GraphLikeSpace.{u,u,u}) (D : CellularDualPair (X := X) (Y := Y) (S := S)),
      D.toFaceDualPair.toDualPair.primal = φ := by
  sorry

/--
Existence milestone: a compact cellular graph-like embedding in the sphere admits a transverse
cellular graph-like dual.  Compactness makes the embedded image closed; it is not folded into the
definition of `GraphLikeSpace`.
-/
theorem Embedding.exists_cellularDual_of_sphere {X : GraphLikeSpace.{u,u,u}} {S : TopCat.{u}}
    (φ : Embedding X S) (hX : X.IsCompact) (hS : IsTopologicalTwoSphere S) (hφ : φ.IsCellular) :
    ∃ (Y : GraphLikeSpace.{u,u,u}) (D : CellularDualPair (X := X) (Y := Y) (S := S)),
      D.toFaceDualPair.toDualPair.primal = φ := by
  let A := Classical.choice (φ.exists_edgeSides_of_surface
    (IsTopologicalTwoSphere.isTopologicalSurface hS) hX)
  let R := Classical.choice (φ.exists_faceSpokeSystem hX hS hφ A)
  let R' := Classical.choice R.exists_dualDrawingData
  exact R'.assembles_cellularDual hX hS hφ

/--
A topological circuit has compact standard subspace; in a second-countable sphere its canonical
pseudo-circle is countable and therefore homeomorphic to the ordinary circle.
-/
theorem CellularDualPair.primalCircuit_is_jordanCurve
    (D : CellularDualPair (X := X) (Y := Y) (S := S))
    (hS : IsTopologicalTwoSphere S) {C : Set X.Edge}
    (hC : X.IsTopologicalCircuit C) : IsSimpleClosedCurve (T := S)
      (D.toFaceDualPair.toDualPair.primal.edgeSetImage C) := by
  sorry

/--
The two Jordan regions give an open bipartition of dual vertices.  Exact transverse intersection
says that its edge boundary is precisely the edges corresponding to `C`; connectivity of face
adjacency inside each region makes this cut minimal.
-/
theorem CellularDualPair.primalCircuit_iff_dualBond
    (D : CellularDualPair (X := X) (Y := Y) (S := S)) (hX : X.IsCompact)
    (hS : IsTopologicalTwoSphere S) (C : Set X.Edge) : X.IsTopologicalCircuit C ↔
      Y.IsTopologicalBond (D.toFaceDualPair.toDualPair.edgeEquiv '' C) := by
  sorry

/--
A primal bond is finite by compactness of the primal space.  Hence the corresponding finite dual
standard subspace is compact and separates the sphere, so the partial Jordan converse supplies a
dual simple closed curve inside it.  Minimality of the primal cut forces that circle to use every
edge of the bond.
-/
theorem CellularDualPair.primalBond_iff_dualCircuit
    (D : CellularDualPair (X := X) (Y := Y) (S := S)) (hX : X.IsCompact)
    (hS : IsTopologicalTwoSphere S) (B : Set X.Edge) : X.IsTopologicalBond B ↔
      Y.IsTopologicalCircuit (D.toFaceDualPair.toDualPair.edgeEquiv '' B) := by
  sorry

/--
On the sphere, a cellular geometric dual is the abstract matroid dual.
This statement is intentionally sphere-specific; it is false on general positive-genus surfaces.
-/
theorem CellularDualPair.isMatroidal_of_sphere (D : CellularDualPair (X := X) (Y := Y) (S := S))
    (hX : X.IsCompact)
    (hS : IsTopologicalTwoSphere S) : D.toFaceDualPair.toDualPair.IsMatroidal := by
  intro M hM
  constructor
  · intro B
    rw [hM.2.2 B]
    exact D.primalBond_iff_dualCircuit hX hS B
  · intro C
    rw [hM.2.1 C]
    exact D.primalCircuit_iff_dualBond hX hS C

end Geometric

/-! ## 5. Pseudosurfaces and defect duality -/

namespace PseudoSurface

variable (S : TopCat.{u})

/--
A pseudosurface is presented by a normalization map from a genuine surface.

No finiteness condition is built in.  A later `FiniteType` predicate can require finitely many
singular points and finite fibres when a theorem needs the classical finite-pseudosurface setting.
-/
structure Model where
  Normalization : TopCat.{u}
  normalization_isSurface : Geometric.IsTopologicalSurface Normalization
  singular : Set S
  normalize : Normalization → S
  quotientMap : IsQuotientMap normalize
  singular_iff_nontrivial_fiber : ∀ y, y ∈ singular ↔
    ∃ x x', x ≠ x' ∧ normalize x = y ∧ normalize x' = y
  regular_isHomeomorph : IsHomeomorph (fun x : {x : Normalization // normalize x ∉ singular} =>
        (⟨normalize x, x.2⟩ : {y : S // y ∉ singular}))

namespace Model

variable {S} (P : Model S)

def IsPinchPoint (p : S) : Prop := p ∈ P.singular

def FiniteType : Prop := P.singular.Finite ∧ ∀ p : S, Set.Finite {x | P.normalize x = p}

/--
A closed pseudosurface has compact normalization and connected quotient.  The normalization itself
may be disconnected: pinching points from distinct surface components is allowed.
-/
def IsClosed : Prop := _root_.IsCompact (univ : Set P.Normalization) ∧ IsConnected (univ : Set S)

/-- The normalization branches lying over a point. -/
abbrev Fiber (p : S) := {x : P.Normalization // P.normalize x = p}

/-- A face is noncellular precisely when it is not an open disk. -/
def IsNoncellularFace {X : GraphLikeSpace.{u,u,u}} (φ : Geometric.Embedding X S) (F : φ.Faces) :
    Prop :=
  ¬ Geometric.IsOpenDisk (φ.faceSet F)

/-- Complement components after pulling the drawing back to the normalization. -/
abbrev NormalizedFaces {X : GraphLikeSpace.{u,u,u}} (φ : Geometric.Embedding X S) :=
  ConnectedComponents {x : P.Normalization // x ∉ P.normalize ⁻¹' range φ.toFun}

/-- The subset of the normalization represented by a normalized face. -/
def normalizedFaceSet {X : GraphLikeSpace.{u,u,u}} (φ : Geometric.Embedding X S)
    (F : P.NormalizedFaces φ) : Set P.Normalization :=
  Subtype.val '' ConnectedComponents.mk ⁻¹' {F}

/--
All complementary regions become disks after normalization.  This excludes noncellularity caused
by handles or other face topology, leaving pinch identifications as the only face defect.
-/
def IsCellularAfterNormalization {X : GraphLikeSpace.{u,u,u}} (φ : Geometric.Embedding X S) : Prop
    :=
  ∀ F : P.NormalizedFaces φ, Geometric.IsOpenDisk (P.normalizedFaceSet φ F)

/-- Pinch points which occur as vertices of this particular embedding. -/
def PinchVertexSet {X : GraphLikeSpace.{u,u,u}} (φ : Geometric.Embedding X S) : Set S :=
  P.singular ∩ range (φ.toFun ∘ X.vertex)

/--
Normal position at the singular locus: every pinch point is used as a vertex by exactly one member
of the dual pair.  The exact-intersection axiom then prevents the other drawing from passing
through that pinch point.
-/
def IsPinchNormal {X Y : GraphLikeSpace.{u,u,u}}
    (D : Geometric.FaceDualPair (X := X) (Y := Y) (S := S)) : Prop :=
  P.singular = P.PinchVertexSet D.toDualPair.primal ∪ P.PinchVertexSet D.toDualPair.dual ∧
  Disjoint (P.PinchVertexSet D.toDualPair.primal) (P.PinchVertexSet D.toDualPair.dual)

/--
The form in which the pinch-point/noncellular-face duality should enter the library.
Only pinch points occupied by primal vertices correspond to noncellular dual faces, and vice
versa.  This distinction is why the witness is attached to an embedding pair rather than merely
to the ambient pseudosurface.
-/
structure DefectDualityWitness {X Y : GraphLikeSpace.{u,u,u}}
    (D : Geometric.FaceDualPair (X := X) (Y := Y) (S := S)) where
  primalPinch_to_dualNoncellular : P.PinchVertexSet D.toDualPair.primal ≃
      {F : D.toDualPair.dual.Faces //
        IsNoncellularFace D.toDualPair.dual F}
  dualPinch_to_primalNoncellular : P.PinchVertexSet D.toDualPair.dual ≃
      {F : D.toDualPair.primal.Faces //
        IsNoncellularFace D.toDualPair.primal F}

/--
An occupied pinch point determines a unique abstract vertex because the embedding and the
graph-like vertex inclusion are injective.
-/
theorem existsUnique_vertex_of_mem_pinchVertexSet {X : GraphLikeSpace.{u,u,u}}
    (φ : Geometric.Embedding X S) (p : P.PinchVertexSet φ) :
    ∃! v : X.Vertex, φ (X.vertex v) = p.1 := by
  sorry

/-- The unique vertex of an embedding situated at an occupied pinch point. -/
noncomputable def vertexAtPinch {X : GraphLikeSpace.{u,u,u}} (φ : Geometric.Embedding X S)
    (p : P.PinchVertexSet φ) : X.Vertex :=
  (P.existsUnique_vertex_of_mem_pinchVertexSet φ p).choose

theorem vertexAtPinch_spec {X : GraphLikeSpace.{u,u,u}} (φ : Geometric.Embedding X S)
    (p : P.PinchVertexSet φ) : φ (X.vertex (P.vertexAtPinch φ p)) = p.1 :=
  (P.existsUnique_vertex_of_mem_pinchVertexSet φ p).choose_spec.1

/-- Distinct occupied pinch points determine distinct vertices. -/
theorem vertexAtPinch_injective {X : GraphLikeSpace.{u,u,u}} (φ : Geometric.Embedding X S) :
    Injective (P.vertexAtPinch φ) := by
  sorry

/-- The dual face paired with a primal pinch vertex. -/
noncomputable def dualFaceOfPrimalPinch {X Y : GraphLikeSpace.{u,u,u}}
    (D : Geometric.FaceDualPair (X := X) (Y := Y) (S := S))
    (p : P.PinchVertexSet D.toDualPair.primal) : D.toDualPair.dual.Faces :=
  D.dualFaceToPrimalVertex.symm (P.vertexAtPinch D.toDualPair.primal p)

/-- The primal face paired with a dual pinch vertex. -/
noncomputable def primalFaceOfDualPinch {X Y : GraphLikeSpace.{u,u,u}}
    (D : Geometric.FaceDualPair (X := X) (Y := Y) (S := S))
    (p : P.PinchVertexSet D.toDualPair.dual) : D.toDualPair.primal.Faces :=
  D.primalFaceToDualVertex.symm (P.vertexAtPinch D.toDualPair.dual p)

/--
Away from `P.singular`, normalization is a homeomorphism.  Thus a face containing no singular
point is homeomorphic to its unique normalized face.  Singular points on the boundary which
belong to the drawing itself are harmless; requiring the closure to avoid them would be too
strong for the defect converse.
-/
theorem regular_face_homeomorphic_normalizedFace {X : GraphLikeSpace.{u,u,u}}
    (φ : Geometric.Embedding X S) (hcell : P.IsCellularAfterNormalization φ) (F : φ.Faces)
    (hregular : Disjoint (φ.faceSet F) P.singular) : Geometric.IsOpenDisk (φ.faceSet F) := by
  sorry

/--
Contrapositively, a noncellular face must actually contain a singular point.  Merely meeting the
singular locus in its boundary does not count.
-/
theorem noncellularFace_contains_singular {X : GraphLikeSpace.{u,u,u}} (φ : Geometric.Embedding X S)
    (hcell : P.IsCellularAfterNormalization φ) (F : φ.Faces) (hF : IsNoncellularFace φ F) :
    ∃ p : S, p ∈ φ.faceSet F ∧ p ∈ P.singular := by
  sorry

/--
A singular point lying in a dual face cannot be occupied by a dual vertex, since faces lie in
the complement of the dual drawing.  Pinch-normality therefore makes it a primal pinch vertex.
-/
theorem singular_mem_dualFace_is_primalPinch {X Y : GraphLikeSpace.{u,u,u}}
    (D : Geometric.FaceDualPair (X := X) (Y := Y) (S := S))
    (hD : P.IsPinchNormal D) {F : D.toDualPair.dual.Faces} {p : S}
    (hpF : p ∈ D.toDualPair.dual.faceSet F) (hpS : p ∈ P.singular) :
    p ∈ P.PinchVertexSet D.toDualPair.primal := by
  sorry

/--
The unique-opposite-vertex field of `FaceDualPair` identifies the face containing an occupied
primal pinch point with the face assigned by `dualFaceOfPrimalPinch`.
-/
theorem dualFaceOfPrimalPinch_eq_of_mem {X Y : GraphLikeSpace.{u,u,u}}
    (D : Geometric.FaceDualPair (X := X) (Y := Y) (S := S))
    (p : P.PinchVertexSet D.toDualPair.primal) (F : D.toDualPair.dual.Faces)
    (hpF : p.1 ∈ D.toDualPair.dual.faceSet F) : P.dualFaceOfPrimalPinch D p = F := by
  have hvF :
      D.toDualPair.primal
          (X.vertex (P.vertexAtPinch D.toDualPair.primal p)) ∈
        D.toDualPair.dual.faceSet F := by
    rw [P.vertexAtPinch_spec D.toDualPair.primal p]
    exact hpF
  have hv := (D.primalVertex_mem_dualFace_iff F _).1 hvF
  simp only [dualFaceOfPrimalPinch, hv, Equiv.symm_apply_apply]

/--
At a pinch vertex, the normalized branches of the opposite face are distinct disks whose images
are identified at the pinch.  Finite type makes the local branch family finite; deleting the
pinch disconnects a punctured neighbourhood, so the quotient face cannot be an open disk.
-/
theorem dualFaceOfPrimalPinch_noncellular {X Y : GraphLikeSpace.{u,u,u}}
    (D : Geometric.FaceDualPair (X := X) (Y := Y) (S := S))
    (hP : P.FiniteType) (hD : P.IsPinchNormal D)
    (hdual : P.IsCellularAfterNormalization D.toDualPair.dual)
    (p : P.PinchVertexSet D.toDualPair.primal) : IsNoncellularFace D.toDualPair.dual
      (P.dualFaceOfPrimalPinch D p) := by
  sorry

/--
Conversely, if a dual face is noncellular, cellularity after normalization says that the only
possible obstruction is an identification over `P.singular`.  Pinch-normality puts the
corresponding singular point at its paired primal vertex.
-/
theorem exists_primalPinch_of_dualFace_noncellular {X Y : GraphLikeSpace.{u,u,u}}
    (D : Geometric.FaceDualPair (X := X) (Y := Y) (S := S)) (hD : P.IsPinchNormal D)
    (hdual : P.IsCellularAfterNormalization D.toDualPair.dual) (F : D.toDualPair.dual.Faces)
    (hF : IsNoncellularFace D.toDualPair.dual F) : ∃ p : P.PinchVertexSet D.toDualPair.primal,
      P.dualFaceOfPrimalPinch D p = F := by
  rcases P.noncellularFace_contains_singular D.toDualPair.dual hdual F hF with
    ⟨p, hpF, hpS⟩
  let p' : P.PinchVertexSet D.toDualPair.primal :=
    ⟨p, P.singular_mem_dualFace_is_primalPinch D hD hpF hpS⟩
  exact ⟨p', P.dualFaceOfPrimalPinch_eq_of_mem D p' F hpF⟩

/-- The canonical map sending a primal pinch point to its defective dual face. -/
noncomputable def primalPinchToDualNoncellular {X Y : GraphLikeSpace.{u,u,u}}
    (D : Geometric.FaceDualPair (X := X) (Y := Y) (S := S))
    (hP : P.FiniteType) (hD : P.IsPinchNormal D)
    (hdual : P.IsCellularAfterNormalization D.toDualPair.dual) :
    P.PinchVertexSet D.toDualPair.primal → {F : D.toDualPair.dual.Faces //
        IsNoncellularFace D.toDualPair.dual F} :=
  fun p => ⟨P.dualFaceOfPrimalPinch D p, P.dualFaceOfPrimalPinch_noncellular D hP hD hdual p⟩

theorem primalPinchToDualNoncellular_injective {X Y : GraphLikeSpace.{u,u,u}}
    (D : Geometric.FaceDualPair (X := X) (Y := Y) (S := S))
    (hP : P.FiniteType) (hD : P.IsPinchNormal D)
    (hdual : P.IsCellularAfterNormalization D.toDualPair.dual) :
    Injective (P.primalPinchToDualNoncellular D hP hD hdual) := by
  intro p q hpq
  apply P.vertexAtPinch_injective D.toDualPair.primal
  apply D.dualFaceToPrimalVertex.symm.injective
  exact congrArg Subtype.val hpq

theorem primalPinchToDualNoncellular_surjective {X Y : GraphLikeSpace.{u,u,u}}
    (D : Geometric.FaceDualPair (X := X) (Y := Y) (S := S))
    (hP : P.FiniteType) (hD : P.IsPinchNormal D)
    (hdual : P.IsCellularAfterNormalization D.toDualPair.dual) :
    Surjective (P.primalPinchToDualNoncellular D hP hD hdual) := by
  rintro ⟨F, hF⟩
  rcases P.exists_primalPinch_of_dualFace_noncellular D hD hdual F hF with
    ⟨p, hp⟩
  use p
  exact Subtype.ext hp

/-- The primal-pinch-to-dual-defect map is bijective. -/
theorem exists_bijective_primalPinch_to_dualNoncellular {X Y : GraphLikeSpace.{u,u,u}}
    (D : Geometric.FaceDualPair (X := X) (Y := Y) (S := S))
    (hP : P.FiniteType) (hD : P.IsPinchNormal D)
    (hdual : P.IsCellularAfterNormalization D.toDualPair.dual) :
    ∃ f : P.PinchVertexSet D.toDualPair.primal → {F : D.toDualPair.dual.Faces //
          IsNoncellularFace D.toDualPair.dual F},
      Bijective f := by
  exact
    ⟨P.primalPinchToDualNoncellular D hP hD hdual,
      P.primalPinchToDualNoncellular_injective D hP hD hdual,
      P.primalPinchToDualNoncellular_surjective D hP hD hdual⟩

/-- The symmetric dual-pinch-to-primal-defect map is bijective. -/
theorem exists_bijective_dualPinch_to_primalNoncellular {X Y : GraphLikeSpace.{u,u,u}}
    (D : Geometric.FaceDualPair (X := X) (Y := Y) (S := S))
    (hP : P.FiniteType) (hD : P.IsPinchNormal D)
    (hprimal : P.IsCellularAfterNormalization D.toDualPair.primal) :
    ∃ f : P.PinchVertexSet D.toDualPair.dual → {F : D.toDualPair.primal.Faces //
          IsNoncellularFace D.toDualPair.primal F},
      Bijective f := by
  sorry

/-- Turn the two bijections into the two equivalences stored by the witness structure. -/
theorem defect_bijections_assemble {X Y : GraphLikeSpace.{u,u,u}}
    (D : Geometric.FaceDualPair (X := X) (Y := Y) (S := S))
    (h₁ : ∃ f : P.PinchVertexSet D.toDualPair.primal → {F : D.toDualPair.dual.Faces //
          IsNoncellularFace D.toDualPair.dual F}, Bijective f)
    (h₂ : ∃ f : P.PinchVertexSet D.toDualPair.dual → {F : D.toDualPair.primal.Faces //
          IsNoncellularFace D.toDualPair.primal F}, Bijective f) :
    Nonempty (P.DefectDualityWitness D) := by
  sorry

/--
Milestone: finite-type normalization and pinch-normal position produce the two defect
correspondences.
-/
theorem exists_defectDualityWitness_of_finiteType {X Y : GraphLikeSpace.{u,u,u}}
    (D : Geometric.FaceDualPair (X := X) (Y := Y) (S := S))
    (hP : P.FiniteType) (hD : P.IsPinchNormal D)
    (hprimal : P.IsCellularAfterNormalization D.toDualPair.primal)
    (hdual : P.IsCellularAfterNormalization D.toDualPair.dual) :
    Nonempty (P.DefectDualityWitness D) := by
  apply P.defect_bijections_assemble D
  · exact P.exists_bijective_primalPinch_to_dualNoncellular D hP hD hdual
  · exact P.exists_bijective_dualPinch_to_primalNoncellular D hP hD hprimal

end Model

end PseudoSurface

/-! ## 6. Matroidal properties and representation targets -/

namespace Matroid

variable {E : Type u} (M : Matroid E)

/-- Graphic, allowing an arbitrary graph on the same edge carrier. -/
def IsGraphic : Prop := ∃ (V : Type u) (G : Graph V E), G.cycleMatroid = M

/-- Cographic means that the abstract dual is graphic. -/
def IsCographic : Prop := IsGraphic M✶

/-- The finite-matroid notion: both graphic and cographic. -/
def IsPlanar : Prop := IsGraphic M ∧ IsCographic M

/-- Every finite isomorphism-minor is graphic. -/
def IsLocallyGraphic : Prop :=
  ∀ {F : Type u} (N : Matroid F), _root_.Matroid.IsoMinor N M → N.Finite → IsGraphic N

/-- Every finite isomorphism-minor is both graphic and cographic. -/
def IsLocallyPlanar : Prop :=
  ∀ {F : Type u} (N : Matroid F), _root_.Matroid.IsoMinor N M → N.Finite → IsPlanar N

/-- The actual hypothesis characterized by graph-like representations. -/
def IsTameLocallyGraphic : Prop := M.Tame ∧ IsLocallyGraphic M

/-- The primal-and-dual graph-like representation class. -/
def IsTameLocallyPlanar : Prop := M.Tame ∧ IsLocallyPlanar M

/-- Representation by some graph-like space, up to matroid isomorphism. -/
def IsGraphLikeRepresentable : Prop := ∃ (X : GraphLikeSpace.{u,u,u}) (N : Matroid X.Edge),
    X.Induces N ∧ Nonempty (M ≂ N)

/-- A ternary cyclic order carried by a specified subset. -/
structure CyclicOrderOn (C : Set E) where
  rel : E → E → E → Prop
  supported : ∀ ⦃a b c⦄, rel a b c → a ∈ C ∧ b ∈ C ∧ c ∈ C
  cyclic : ∀ ⦃a b c⦄, rel a b c → rel b c a
  asymmetric : ∀ ⦃a b c⦄, rel a b c → ¬ rel c b a
  transitive : ∀ ⦃a b c d⦄, rel a b c → rel a c d → rel a b d
  total : ∀ ⦃a b c⦄, a ∈ C → b ∈ C → c ∈ C → a ≠ b → b ≠ c → a ≠ c → rel a b c ∨ rel c b a

/-- Clockwise adjacency after restricting a cyclic order to `T`. -/
def CyclicOrderOn.ClockwiseAdjacent {C : Set E} (R : CyclicOrderOn C) (T : Set E) (p q : E) : Prop
    :=
  p ∈ T ∧ q ∈ T ∧ p ≠ q ∧ ∀ ⦃g⦄, g ∈ T → g ≠ p → g ≠ q → R.rel p q g

/-- Multiplication of signs when `true` represents `+1` and `false` represents `-1`. -/
def signMul (a b : Bool) : Bool := a == b

/--
The finitary auxiliary structure from Bowler--Carmesin--Christian, Definition 6.2.  It records
orientations of circuits and bonds, the side of each non-bond edge, the induced cyclic circuit
orders, signing balance, and the four adjacency compatibility rules.
-/
structure GraphFramework where
  circuitOrder : ∀ (C : Set E), M.IsCircuit C → CyclicOrderOn C
  circuitSign : ∀ (C : Set E), M.IsCircuit C → E → Bool
  cocircuitSign : ∀ (B : Set E), M.IsCocircuit B → E → Bool
  sideSign : ∀ (B : Set E), M.IsCocircuit B → E → Bool
  signing_balance : ∀ (C B : Set E) (hC : M.IsCircuit C) (hB : M.IsCocircuit B),
    {e | e ∈ C ∩ B ∧ signMul (circuitSign C hC e) (cocircuitSign B hB e) = true}.encard =
    {e | e ∈ C ∩ B ∧ signMul (circuitSign C hC e) (cocircuitSign B hB e) = false}.encard
  order_characterization : ∀ (C : Set E) (hC : M.IsCircuit C)
      ⦃e f g : E⦄, e ≠ f → f ≠ g → e ≠ g → e ∈ C → f ∈ C → g ∈ C →
    (circuitOrder C hC).rel e f g ↔ ∃ (B : Set E) (hB : M.IsCocircuit B),
        C ∩ B = {e, f} ∧ sideSign B hB g = signMul (circuitSign C hC f) (cocircuitSign B hB f)
  adjacent_compatibility : ∀ (C B T : Set E) (hC : M.IsCircuit C) (hB : M.IsCocircuit B),
      C ∩ B ⊆ T → T ⊆ C → T.Finite → ∀ ⦃p q : E⦄,
      (circuitOrder C hC).ClockwiseAdjacent T p q → (p ∈ B ∧ q ∈ B → signMul
        (circuitSign C hC p) (cocircuitSign B hB p) =
          !(signMul (circuitSign C hC q) (cocircuitSign B hB q))) ∧
      (p ∉ B ∧ q ∉ B → sideSign B hB p = sideSign B hB q) ∧ (p ∈ B ∧ q ∉ B → signMul
        (circuitSign C hC p) (cocircuitSign B hB p) = sideSign B hB q) ∧
      (p ∉ B ∧ q ∈ B → signMul (circuitSign C hC q) (cocircuitSign B hB q) = !(sideSign B hB p))

/--
Compactness of a topological pseudo-circle makes its intersection with an ambient-open bond
finite.  Hence every matroid induced by a graph-like space is tame.
-/
theorem GraphLikeSpace.Induces.tame {X : GraphLikeSpace.{u,u,u}} {N : Matroid X.Edge}
    (hN : X.Induces N) : N.Tame := by
  refine ⟨?_⟩
  intro Z hZ
  rcases hZ with ⟨C, B, hC, hB, rfl⟩
  exact X.topologicalCircuit_inter_topologicalCut_finite
    ((hN.2.1 C).1 hC) ((hN.2.2 B).1 hB).prop.2

/--
Restriction and contraction models realize deletion and contraction of an induced matroid.
After any finite isomorphism-minor, the resulting finite graph-like space is homeomorphic to its
incidence graph realization, so that minor is graphic.
-/
theorem GraphLikeSpace.Induces.finiteIsoMinor_graphic {X : GraphLikeSpace.{u,u,u}}
    {N : Matroid X.Edge} (hN : X.Induces N) {F : Type u} (N' : Matroid F)
    (hminor : _root_.Matroid.IsoMinor N' N) (hfinite : N'.Finite) : IsGraphic N' := by
  sorry

/-- The easy direction of the BCC representation theorem, including transport across isomorphism. -/
theorem graphLikeRepresentable_tameLocallyGraphic (hM : IsGraphLikeRepresentable M) :
    IsTameLocallyGraphic M := by
  sorry

/-- A finite graphic matroid receives a graph framework from an oriented finite graph. -/
theorem finiteGraphic_hasGraphFramework (hMfin : M.Finite) (hMgraphic : IsGraphic M) :
    Nonempty (GraphFramework M) := by
  sorry

/--
Finite-minor approximation lemma used by framework compactness.  A finite collection of circuits,
cocircuits, and observed edges can be preserved inside one finite minor, including all of the
listed circuit--cocircuit intersections.
-/
theorem Tame.exists_finiteMinor_preserving_traces (hM : M.Tame)
    (circuits cocircuits : Finset (Set E)) (observed : Finset E) : ∃ N : Matroid E,
      N.Finite ∧ Nonempty (_root_.Matroid.IsoMinor N M) ∧ (∀ C ∈ circuits, M.IsCircuit C →
        ∃ C', N.IsCircuit C' ∧ C' ∩ observed = C ∩ observed) ∧
      (∀ B ∈ cocircuits, M.IsCocircuit B →
        ∃ B', N.IsCocircuit B' ∧ B' ∩ observed = B ∩ observed) := by
  sorry

/--
Framework compactness (BCC Lemma 6.4).  Encode every sign and ternary-order choice in a product
of copies of `Bool`.  Each framework axiom is closed and depends on finitely many coordinates.
The preceding finite-minor lemma proves the finite-intersection property; compactness of the
product supplies a global framework.
-/
theorem tameLocallyGraphic_hasGraphFramework (hM : IsTameLocallyGraphic M) :
    Nonempty (GraphFramework M) := by
  sorry

/--
The intermediate output of the framework construction.  Besides the space and edge
identification it records the two inclusions needed by the matroid-recognition argument; neither
inclusion is silently folded into `Induces`.
-/
structure GraphFramework.TopologicalModel (F : GraphFramework M) where
  space : GraphLikeSpace.{u,u,u}
  edgeEquiv : E ≃ space.Edge
  circuit_to_topologicalCircuit : ∀ C : Set E, M.IsCircuit C →
      space.IsTopologicalCircuit (edgeEquiv '' C)
  cocircuit_to_topologicalCut : ∀ B : Set E, M.IsCocircuit B →
      space.IsTopologicalCut (edgeEquiv '' B)

/--
Take vertices to be all sign vectors on the cocircuits.  The two endpoints of an edge are given
coordinatewise by `sideSign` off a cocircuit and by the two opposite `cocircuitSign` values on
it.  Generate the topology from open edge intervals and signed cocircuit half-spaces.

Continuity of the endpoint paths is a coordinate calculation; two different sign vectors are
separated by the halfspaces at a coordinate where they differ.  Circuit cyclic orders then give
the maps from canonical pseudo-circles, while the two signed halfspaces of a cocircuit exhibit its
image as a topological cut.
-/
theorem GraphFramework.exists_topologicalModel (F : GraphFramework M) (hMtame : M.Tame) :
    Nonempty (GraphFramework.TopologicalModel M F) := by
  sorry

/--
The carrier-level graph-like-space existence statement extracted from the preceding structured
model.
-/
theorem GraphFramework.exists_graphLikeSpace (F : GraphFramework M) (hMtame : M.Tame) :
    ∃ X : GraphLikeSpace.{u,u,u}, Nonempty (E ≃ X.Edge) := by
  rcases GraphFramework.exists_topologicalModel (M := M) F hMtame with ⟨R⟩
  exact ⟨R.space, ⟨R.edgeEquiv⟩⟩

/--
Matroid recognition (BCC Lemma 2.7).  Pull all topological circuits and cuts back along
`edgeEquiv`.  The model supplies every circuit and cocircuit of `M`; the previously proved fact
that a topological circuit and topological cut never meet in one edge supplies orthogonality.
Circuit/cocircuit elimination then shows that there are no extra topological circuits and that
the minimal nonempty topological cuts are exactly the cocircuits.
-/
theorem GraphFramework.TopologicalModel.exists_inducedMatroid {F : GraphFramework M}
    (R : GraphFramework.TopologicalModel M F) : ∃ N : Matroid R.space.Edge,
      R.space.Induces N ∧ Nonempty (M ≂ N) := by
  sorry

/--
Framework construction, part 2 (BCC Lemmas 6.7--6.12), assembled through the explicit
topological-model and recognition milestones.
-/
theorem GraphFramework.exists_inducingGraphLikeSpace (F : GraphFramework M) (hMtame : M.Tame) :
    ∃ (X : GraphLikeSpace.{u,u,u}) (N : Matroid X.Edge), X.Induces N ∧ Nonempty (M ≂ N) := by
  let R := Classical.choice
    (GraphFramework.exists_topologicalModel (M := M) F hMtame)
  rcases GraphFramework.TopologicalModel.exists_inducedMatroid
    (M := M) R with ⟨N, hN, hMN⟩
  exact ⟨R.space, N, hN, hMN⟩

/-- The compactness/framework direction of the BCC representation theorem. -/
theorem tameLocallyGraphic_graphLikeRepresentable (hM : IsTameLocallyGraphic M) :
    IsGraphLikeRepresentable M := by
  rcases tameLocallyGraphic_hasGraphFramework M hM with ⟨F⟩
  exact GraphFramework.exists_inducingGraphLikeSpace (M := M) F hM.1

theorem graphLikeRepresentable_iff_tameLocallyGraphic :
    IsGraphLikeRepresentable M ↔ IsTameLocallyGraphic M := by
  exact ⟨graphLikeRepresentable_tameLocallyGraphic M,
    tameLocallyGraphic_graphLikeRepresentable M⟩

/-- Local planarity is exactly local graphicness of both the matroid and its dual. -/
theorem locallyPlanar_iff_locallyGraphic_and_dual :
    IsLocallyPlanar M ↔ IsLocallyGraphic M ∧ IsLocallyGraphic M✶ := by
  sorry

/-- Tameness is invariant under matroid duality. -/
theorem tame_dual_iff : M✶.Tame ↔ M.Tame := by
  exact _root_.Matroid.tame_dual_iff

/-- Add tameness to the preceding local equivalence. -/
theorem tameLocallyPlanar_iff_tameLocallyGraphic_and_dual : IsTameLocallyPlanar M ↔
      IsTameLocallyGraphic M ∧ IsTameLocallyGraphic M✶ := by
  sorry

theorem tameLocallyPlanar_iff_graphLike_primal_and_dual : IsTameLocallyPlanar M ↔
      IsGraphLikeRepresentable M ∧ IsGraphLikeRepresentable M✶ := by
  rw [graphLikeRepresentable_iff_tameLocallyGraphic,
    graphLikeRepresentable_iff_tameLocallyGraphic]
  exact tameLocallyPlanar_iff_tameLocallyGraphic_and_dual M

/-- The dual of a finite planar matroid is finite and planar. -/
theorem IsPlanar.dual {N : Matroid E} (hN : IsPlanar N) : IsPlanar N✶ := by
  sorry

/--
A finite isomorphism-minor of `M✶` dualizes to a finite isomorphism-minor of `M`; apply local
planarity there and dualize the resulting planar structure.
-/
theorem IsLocallyPlanar.dual_aux (hM : IsLocallyPlanar M) {F : Type u} (N : Matroid F)
    (hNM : _root_.Matroid.IsoMinor N M✶) (hNfin : N.Finite) : IsPlanar N := by
  sorry

theorem IsLocallyPlanar.dual (hM : IsLocallyPlanar M) : IsLocallyPlanar M✶ := by
  exact hM.dual_aux

/--
Composition of isomorphism-minors reduces a finite isomorphism-minor of `N` to one of `M`.
-/
theorem IsLocallyPlanar.isoMinor_aux {F K : Type u} {N : Matroid F} (hM : IsLocallyPlanar M)
    (hNM : _root_.Matroid.IsoMinor N M) (L : Matroid K) (hLN : _root_.Matroid.IsoMinor L N)
    (hLfin : L.Finite) : IsPlanar L := by
  sorry

theorem IsLocallyPlanar.isoMinor {F : Type u} {N : Matroid F} (hM : IsLocallyPlanar M)
    (hNM : _root_.Matroid.IsoMinor N M) : IsLocallyPlanar N := by
  intro K L hLN hLfin
  exact IsLocallyPlanar.isoMinor_aux (M := M) hM hNM L hLN hLfin

/--
Finite crossing preservation: if a finite set is a circuit--cocircuit intersection in `M`, a
finite isomorphism-minor preserves that same crossing.  Contract outside a spanning extension of
the circuit and delete outside a cospanning extension of the cocircuit.
-/
theorem IsCrossing.exists_finiteIsoMinor_preserving {X : Finset E} (hX : M.IsCrossing X) :
    ∃ N : Matroid E, N.Finite ∧ Nonempty (_root_.Matroid.IsoMinor N M) ∧ N.IsCrossing X := by
  sorry

/--
A finite matroid that is both graphic and cographic is regular; in particular every crossing has
even cardinality.
-/
theorem finitePlanar_crossing_even {N : Matroid E} (hNfin : N.Finite) (hN : IsPlanar N)
    {X : Finset E} (hX : N.IsCrossing X) : Even X.card := by
  sorry

/--
For infinite matroids, `CrossingBinary` (every finite circuit--cocircuit intersection is even) is
the correct unconditional binary conclusion.
-/
theorem IsLocallyPlanar.crossingBinary (hM : IsLocallyPlanar M) : M.CrossingBinary := by
  intro X hX
  rcases IsCrossing.exists_finiteIsoMinor_preserving (M := M) (X := X) hX with
    ⟨N, hNfin, ⟨hNM⟩, hNX⟩
  exact finitePlanar_crossing_even hNfin (hM N hNM hNfin) hNX

/--
Ordinary vector-space representability is a finitary notion in the current library.  Thus it is
available from local planarity only after adding `Finitary M`.
-/
theorem IsLocallyPlanar.representableGF2 [M.Finitary] (hM : IsLocallyPlanar M) :
    M.Representable (ZMod 2) := by
  exact (_root_.Matroid.crossingBinary_iff_representable (M := M)).mp hM.crossingBinary

/-- Finite graphic-and-cographic matroids are regular and hence representable over every field. -/
theorem finitePlanar_representable {K : Type u} [Field K] {N : Matroid E} (hNfin : N.Finite)
    (hN : IsPlanar N) : N.Representable K := by
  sorry

/-- Every finite minor is representable over every field (indeed, it is regular). -/
theorem IsLocallyPlanar.finiteMinor_representable {F K : Type u} [Field K] {N : Matroid F}
    (hM : IsLocallyPlanar M) (hNM : _root_.Matroid.IsoMinor N M) (hNfin : N.Finite) :
    N.Representable K := by
  exact finitePlanar_representable hNfin (hM N hNM hNfin)

/-! ### Thin-sums representability (the non-finitary target) -/

variable {F A : Type u} [Field F]

/--
`c` is a thin dependence of the family `a` if every coordinate sum has finite support and is zero.
The finite witness avoids imposing a topology on the coefficient field.
-/
def IsThinDependence (a : E → A → F) (c : E → F) : Prop := ∀ i : A, ∃ s : Finset E,
    (∀ e, c e * a e i ≠ 0 → e ∈ s) ∧ ∑ e ∈ s, c e * a e i = 0

def ThinIndependent (a : E → A → F) (S : Set E) : Prop :=
  ∀ c : E → F, IsThinDependence a c → support c ⊆ S → c = 0

/-- A thin-sums representation, separated from ordinary `Matroid.Representable`. -/
structure ThinSumsRepresentation where
  coordinate : Type u
  family : E → coordinate → F
  indep_iff : ∀ S, M.Indep S ↔ ThinIndependent family S

def IsThinSumsRepresentable : Prop := Nonempty (ThinSumsRepresentation (F := F) M)

/--
Finite-field compactness theorem for thin sums.  Put all prospective matrix coordinates in a
product of copies of the finite discrete field.  For every finite family of desired dependencies
and independencies impose the corresponding finite closed constraints.  Finite minors supply
solutions to every finite constraint family; compactness gives one global family.  Tameness
identifies its thin dependencies with the circuits of `M`.
-/
theorem tame_thinSums_of_finiteMinor_representable [Fintype F] (hMtame : M.Tame)
    (hfinite : ∀ {K : Type u} (N : Matroid K),
      _root_.Matroid.IsoMinor N M → N.Finite → N.Representable F) :
    IsThinSumsRepresentable (F := F) M := by
  sorry

/--
Every finite minor of a locally planar matroid is regular.  With tameness added, the finite-field
compactness theorem therefore gives thin-sums representations over every finite field.
-/
theorem IsTameLocallyPlanar.thinSumsRepresentable [Fintype F] (hM : IsTameLocallyPlanar M) :
    IsThinSumsRepresentable (F := F) M := by
  apply tame_thinSums_of_finiteMinor_representable (M := M) (F := F) hM.1
  intro K N hNM hNfin
  exact IsLocallyPlanar.finiteMinor_representable
    (M := M) (K := F) hM.2 hNM hNfin

end Matroid

/-! ## Proposed dependency order

1. Prove the elementary API for `GraphLikeSpace`, cuts, maps, and restrictions.
2. Finish `OrderedPseudoLine.space`, then pseudo-circles and topological circuits.
3. Construct contraction and prove that induced matroids commute with minors.
4. Relate ordinary graph realizations to graph-like spaces and prove the weak/metric comparison.
5. Formalize faces and edge-side data for surface embeddings.
6. Prove existence of the generally noncompact spherical geometric dual, then prove its
   circuit--bond correspondence; keep positive-genus cellular duality separate.
7. Add normalization examples and prove the pinch-point/noncellular-face correspondence under
   `IsPinchNormal`.
8. Port the BCC graph-framework compactness argument to obtain abstract graph-like
   representations.
9. Keep the three representation conclusions distinct: `CrossingBinary` without extra
   hypotheses, ordinary `GF(2)` representation for finitary matroids, and finite-field
   thin-sums representation for tame matroids.
-/

end GraphEmbeddingBlueprint
/-!
## 7. Kuratowski's theorem for finite graphs

This section connects the ordinary-graph realization developed in Section 3 to the repository's
existing topological-minor API.  The target is the topological form of Kuratowski's theorem for
finite graphs, including loops and parallel edges:

* a finite graph is planar exactly when it has no topological `K₅` and no topological `K₃,₃`;
* the easy implication uses preservation of planarity under topological minors;
* the hard implication reduces first to connected simple 3-connected graphs and then uses strong
  induction on the number of edges;
* the inductive contraction step is deliberately isolated.  Its proof is intended to combine
  `Graph.Drawing.exists_facial_cycle_of_delete_vertex`, `Graph.K33_K5_lemma`, and
  `Graph.Drawing.isPlanar_of_contract_of_facial_cycle_two_paths`.

Keeping this section in a separate namespace avoids committing the eventual library theorem names
while the reduction interfaces are still being proved.
-/

namespace GraphEmbeddingBlueprint
namespace Kuratowski

open Graph

variable {α β γ δ : Type*}

/-- Planarity in this section is the weak-realization drawing notion from Section 3.

This is definitionally the same intended topological formulation as `Graph.IsPlanar` in
`Matroid.Graph.Planarity.Drawing`; the local name avoids importing two currently incompatible
plane-topology developments into this blueprint file.
-/
abbrev IsPlanar (G : Graph α β) : Prop := Realization.IsDrawablePlanar G

/-- Planarity of weak realizations is inherited by topological minors. -/
theorem IsPlanar.of_isTopologicalMinor {J : Graph γ δ} {G : Graph α β}
    (hG : IsPlanar G) (hJG : J.IsTopologicalMinor G) : IsPlanar J := by
  sorry

/-- The weak realization of `K₅` has no plane drawing. -/
theorem not_isPlanar_completeGraph_five : ¬ IsPlanar (CompleteGraph 5) := by
  sorry

/-- The weak realization of `K₃,₃` has no plane drawing. -/
theorem not_isPlanar_completeBipartiteGraph_three_three :
    ¬ IsPlanar (CompleteBipartiteGraph 3 3) := by
  sorry

/-- A graph contains one of the two subdivisions forbidden by Kuratowski's theorem. -/
def HasKuratowskiObstruction (G : Graph α β) : Prop :=
  (CompleteGraph 5).IsTopologicalMinor G ∨
    (CompleteBipartiteGraph 3 3).IsTopologicalMinor G

/-- The paired non-containment hypothesis in the topological form of Kuratowski's theorem. -/
def IsKuratowskiFree (G : Graph α β) : Prop :=
  ¬ (CompleteGraph 5).IsTopologicalMinor G ∧
    ¬ (CompleteBipartiteGraph 3 3).IsTopologicalMinor G

/-- The positive and negative obstruction packages are logical complements. -/
theorem isKuratowskiFree_iff_not_hasKuratowskiObstruction (G : Graph α β) :
    IsKuratowskiFree G ↔ ¬ HasKuratowskiObstruction G := by
  simp [IsKuratowskiFree, HasKuratowskiObstruction]

/-- The easy direction: a planar graph contains neither forbidden topological minor. -/
theorem isKuratowskiFree_of_isPlanar {G : Graph α β} (hG : IsPlanar G) :
    IsKuratowskiFree G := by
  constructor
  · intro hK5
    exact not_isPlanar_completeGraph_five (hG.of_isTopologicalMinor hK5)
  · intro hK33
    exact not_isPlanar_completeBipartiteGraph_three_three (hG.of_isTopologicalMinor hK33)

/-- Kuratowski-freeness descends to topological minors.

The proof composes topological models.  This is the monotonicity interface needed every time a
smaller graph is extracted during the connectivity reductions.
-/
theorem IsKuratowskiFree.of_isTopologicalMinor {J : Graph γ δ} {G : Graph α β}
    (hG : IsKuratowskiFree G) (hJG : J.IsTopologicalMinor G) : IsKuratowskiFree J := by
  sorry

/-- Reduction from arbitrary finite graphs to the connected case.

The eventual proof draws connected components in pairwise disjoint disks.  Conversely, any
forbidden topological model is connected and therefore lies in a single component.  Quantifying
over same-carrier graphs keeps this milestone independent of the final connected-component API.
-/
theorem isPlanar_of_connected_case {G : Graph α β} [G.Finite]
    (hconnected : ∀ H : Graph α β, H.Finite → H.Connected →
      IsKuratowskiFree H → IsPlanar H)
    (hG : IsKuratowskiFree G) : IsPlanar G := by
  sorry

/-- Reduction from connected finite graphs to simple 3-connected graphs.

Loops and redundant parallel edges are restored inside small vertex disks.  Cut vertices are
handled by gluing block drawings at one point, and 2-separations by drawing the two augmented
sides on opposite sides of a virtual edge.  Kuratowski-freeness of every extracted side follows
from `IsKuratowskiFree.of_isTopologicalMinor`.
-/
theorem isPlanar_of_threeConnected_case {G : Graph α β} [G.Finite]
    (hGconn : G.Connected) (hGfree : IsKuratowskiFree G)
    (hthree : ∀ H : Graph α β, H.Finite → H.Simple → H.ConnGE 3 →
      IsKuratowskiFree H → IsPlanar H) : IsPlanar G := by
  sorry

/-- Small base case for the 3-connected induction.

A finite simple 3-connected graph with at most six edges has a direct plane drawing (the extremal
case is `K₄`).
-/
theorem isPlanar_of_connGE_three_of_edgeSet_ncard_le_six {G : Graph α β}
    [G.Finite] [G.Simple] (hG3 : G.ConnGE 3) (hE : E(G).ncard ≤ 6) : IsPlanar G := by
  sorry

/-- The local contraction/facial-cycle step at the heart of the hard implication.

Choose a plane drawing of the contraction and use its facial cycle around the contracted vertex.
Applied to the two original endpoints, `Graph.K33_K5_lemma` gives either the two clean boundary
paths required by `Graph.Drawing.isPlanar_of_contract_of_facial_cycle_two_paths`, or an explicit
topological `K₅`/`K₃,₃` in `G`.  Simplicity is stated explicitly for the contraction because a
later proof may obtain it by deleting redundant parallel edges before applying this lemma.
-/
theorem isPlanar_or_hasKuratowskiObstruction_of_contract {G : Graph α β} {e : β} {u v : α}
    [G.Finite] [G.Simple] (he : G.IsLink e u v) (huv : u ≠ v)
    (hcontractFinite : (G /(e, he)).Finite)
    (hcontractSimple : (G /(e, he)).Simple)
    (hcontract3 : (G /(e, he)).ConnGE 3)
    (hcontractPlanar : IsPlanar (G /(e, he))) :
    IsPlanar G ∨ HasKuratowskiObstruction G := by
  sorry

/-- Strong-induction step for a simple 3-connected Kuratowski-free graph.

The proof chooses an edge and a suitable simple core of its contraction.  Smaller 3-connected
cores are planar by `ih`; the preceding contraction lemma then either reconstructs a drawing of
`G` or contradicts Kuratowski-freeness.  Separating pairs created by contraction are delegated to
the 2-separation gluing argument from `isPlanar_of_threeConnected_case`.
-/
theorem connGE_three_induction_step {G : Graph α β} [G.Finite] [G.Simple]
    (hG3 : G.ConnGE 3) (hGfree : IsKuratowskiFree G)
    (ih : ∀ H : Graph α β, H.Finite → H.Simple → H.ConnGE 3 →
      E(H).ncard < E(G).ncard → IsKuratowskiFree H → IsPlanar H) : IsPlanar G := by
  sorry

/-- The hard implication for finite simple 3-connected graphs. -/
theorem isPlanar_of_isKuratowskiFree_of_connGE_three {G : Graph α β}
    [G.Finite] [G.Simple] (hG3 : G.ConnGE 3) (hGfree : IsKuratowskiFree G) :
    IsPlanar G := by
  sorry

/-- The hard implication for connected finite graphs, assembled from the connectivity reduction
and the 3-connected induction. -/
theorem isPlanar_of_isKuratowskiFree_of_connected {G : Graph α β} [G.Finite]
    (hGconn : G.Connected) (hGfree : IsKuratowskiFree G) : IsPlanar G := by
  apply isPlanar_of_threeConnected_case hGconn hGfree
  intro H hHfinite hHsimple hH3 hHfree
  letI := hHfinite
  letI := hHsimple
  exact isPlanar_of_isKuratowskiFree_of_connGE_three hH3 hHfree

/-- The hard implication for arbitrary finite graphs. -/
theorem isPlanar_of_isKuratowskiFree {G : Graph α β} [G.Finite]
    (hGfree : IsKuratowskiFree G) : IsPlanar G := by
  apply isPlanar_of_connected_case (G := G) (hG := hGfree)
  intro H hHfinite hHconn hHfree
  letI := hHfinite
  exact isPlanar_of_isKuratowskiFree_of_connected hHconn hHfree

/-- **Kuratowski's theorem (finite topological form).**

A finite graph is planar if and only if it contains neither a subdivision of `K₅` nor a
subdivision of `K₃,₃`.
-/
theorem kuratowski {G : Graph α β} [G.Finite] :
    IsPlanar G ↔ IsKuratowskiFree G := by
  exact ⟨isKuratowskiFree_of_isPlanar, isPlanar_of_isKuratowskiFree⟩

/-- Equivalent positive-obstruction formulation of Kuratowski's theorem. -/
theorem not_isPlanar_iff_hasKuratowskiObstruction {G : Graph α β} [G.Finite] :
    ¬ IsPlanar G ↔ HasKuratowskiObstruction G := by
  classical
  rw [kuratowski, isKuratowskiFree_iff_not_hasKuratowskiObstruction]
  constructor
  · intro h
    exact Classical.byContradiction fun hn => h hn
  · intro h hn
    exact hn h

end Kuratowski
end GraphEmbeddingBlueprint
