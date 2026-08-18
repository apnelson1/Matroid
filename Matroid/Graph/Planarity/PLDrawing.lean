module

public import Matroid.Graph.Planarity.Drawing
public import Matroid.ForMathlib.Geometry.PolygonalPath.SimpleArcOrLoop

@[expose] public section

/-!
# Polygonal drawings

A drawing is *polygonal*, or *PL*, when the image of every edge is a finite union of segments. This
file gives that notion two forms: `Graph.PLDrawing` stores a polygonal path for every edge, while
`Graph.Drawing.IsPL` asserts that such paths exist. The edge condition is stated on the path image,
and `cell_isSimpleArcOrLoop` records that the stored path is embedded. Loops are handled by
`PolygonalPath.IsSimpleArcOrLoop`.

The definitions work over a real topological vector space. Plane-specific results use
`EuclideanSpace ℝ (Fin 2)` and take faces after transporting a drawing to its one-point
compactification.

## Main definitions

* `Graph.PLDrawing` : a drawing together with a polygonal path realising each edge.
* `Graph.Drawing.IsPL` : the drawing is polygonal.
* `Graph.PLPlanar` : the graph has a polygonal drawing in the plane.

## Main statements

* `Graph.exists_plDrawing_of_cells` : build a polygonal drawing from vertex positions and cells.
* `Graph.Drawing.IsPL.restrict` : a subgraph of a polygonal drawing is polygonally drawn.
* `Graph.PLDrawing.exists_nhds_inter_support_eq_segment` : the local edge-interior description.

The reduction `Planar ↔ PLPlanar` is in `Matroid.Graph.Planarity.PLReduction`, which is where the
approximation lemmas are used.
-/

open Function Set Topology

namespace Graph

noncomputable section

variable {α β : Type*} {G H : Graph α β} {e : β} {u v : α}

/-- A polygonal drawing of `G` in `V`: a drawing together with, for each edge, a polygonal path
whose image is the closed cell of that edge. -/
structure PLDrawing (G : Graph α β) (V : Type*) [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [ContinuousSMul ℝ V] [ContinuousAdd V] extends Drawing G V where
  /-- The polygonal path realising the edge `e`. -/
  cell : ∀ e : E(G), PolygonalPath (toDrawing.vertex (edgeSource e))
    (toDrawing.vertex (edgeTarget e))
  /-- Each cell is an embedded arc, or an embedded circle when the edge is a loop. -/
  cell_isSimpleArcOrLoop : ∀ e, (cell e).IsSimpleArcOrLoop
  /-- Each cell traces out exactly the closed cell of its edge. -/
  range_edgePath : ∀ e, range (toDrawing.edgePath e) = (cell e).toSet

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [ContinuousSMul ℝ V]

/-- A drawing is polygonal when every closed cell is the image of an embedded polygonal arc or
circle. The witnesses are not canonical — subdivision, reversal and the orientation of the edge all
change them — so they are existentially quantified here and carried by `PLDrawing` where a
construction needs them. -/
def Drawing.IsPL [ContinuousAdd V] (D : Drawing G V) : Prop :=
  ∀ e : E(G), ∃ P : PolygonalPath (D.vertex (edgeSource e)) (D.vertex (edgeTarget e)),
    P.IsSimpleArcOrLoop ∧ range (D.edgePath e) = P.toSet

namespace PLDrawing

variable [ContinuousAdd V] {D : PLDrawing G V}

lemma isPL (D : PLDrawing G V) : D.IsPL :=
  fun e ↦ ⟨D.cell e, D.cell_isSimpleArcOrLoop e, D.range_edgePath e⟩

/-- Restrict a polygonal drawing to a subgraph. The cells transport unchanged: a subgraph has the
same ends for each of its edges, and the orientation of an edge is determined by its ends — `ArbRel`
fixes one linear order per *type*, so `IsSubgraph.source` and `IsSubgraph.target` hold — so all that
is needed is the propositional retyping of the endpoints, `PolygonalPath.cast`. No reversal. -/
def restrictCell (D : PLDrawing G V) (h : H ≤ G) (e : E(H)) :
    PolygonalPath ((D.restrict h).vertex (edgeSource e))
      ((D.restrict h).vertex (edgeTarget e)) :=
  (D.cell ⟨e.1, edgeSet_mono h e.2⟩).cast (D.restrict_vertex_edgeSource h e).symm
    (D.restrict_vertex_edgeTarget h e).symm

theorem isSimpleArcOrLoop_restrictCell (D : PLDrawing G V) (h : H ≤ G) (e : E(H)) :
    (D.restrictCell h e).IsSimpleArcOrLoop :=
  (PolygonalPath.isSimpleArcOrLoop_cast ..).mpr
    (D.cell_isSimpleArcOrLoop ⟨e.1, edgeSet_mono h e.2⟩)

theorem range_edgePath_restrictCell (D : PLDrawing G V) (h : H ≤ G) (e : E(H)) :
    range ((D.restrict h).edgePath e) = (D.restrictCell h e).toSet := by
  rw [Drawing.range_edgePath_restrict, restrictCell, PolygonalPath.toSet_cast, D.range_edgePath]

def restrict (D : PLDrawing G V) (h : H ≤ G) : PLDrawing H V where
  toDrawing := D.toDrawing.restrict h
  cell := D.restrictCell h
  cell_isSimpleArcOrLoop := D.isSimpleArcOrLoop_restrictCell h
  range_edgePath := D.range_edgePath_restrictCell h

@[simp]
lemma restrict_toDrawing (D : PLDrawing G V) (h : H ≤ G) :
    (D.restrict h).toDrawing = D.toDrawing.restrict h := rfl

/-- The support of a polygonal drawing of a finite graph is a finite union of segments together
with the vertex images. -/
theorem exists_finite_support [G.Finite] (D : PLDrawing G V) :
    ∃ S : Set (V × V), S.Finite ∧ D.support = range D.vertex ∪ ⋃ s ∈ S, segment ℝ s.1 s.2 := by
  let S : Set (V × V) := ⋃ e : E(G), {s | s ∈ (D.cell e).edges}
  refine ⟨S, finite_iUnion fun e ↦ (D.cell e).edges.finite_toSet, ?_⟩
  rw [Drawing.support_eq]
  refine subset_antisymm ?_ ?_ <;> rintro x (hx | hx)
  · exact Or.inl hx
  · obtain ⟨e, he⟩ := mem_iUnion.mp hx
    have hx' : x ∈ (D.cell e).toSet := by rwa [← D.range_edgePath e]
    rw [PolygonalPath.toSet_eq_insert_biUnion] at hx'
    obtain hx' | hx' := mem_insert_iff.mp hx'
    · exact Or.inl ⟨edgeTarget e, hx'.symm⟩
    · obtain ⟨s, hs, hseg⟩ := mem_iUnion₂.mp hx'
      exact Or.inr <| mem_iUnion₂.mpr ⟨s, mem_iUnion.mpr ⟨e, hs⟩, hseg⟩
  · exact Or.inl hx
  · obtain ⟨s, hsS, hseg⟩ := mem_iUnion₂.mp hx
    obtain ⟨e, hs⟩ := mem_iUnion.mp hsS
    refine Or.inr <| mem_iUnion.mpr ⟨e, ?_⟩
    rw [D.range_edgePath e, PolygonalPath.toSet_eq_insert_biUnion]
    exact mem_insert_of_mem _ (mem_iUnion₂.mpr ⟨s, hs, hseg⟩)

end PLDrawing

/-- Near a point interior to one cell, the support agrees locally with a single segment of that
cell. The vertex case is given by the star lemma. -/
theorem exists_nhds_inter_support_eq_segment [G.Finite] [T2Space V] [IsTopologicalAddGroup V]
    (D : PLDrawing G V) {f : E(G)} {a : V} (ha : a ∈ (D.cell f).toSet)
    (hav : a ∉ (D.cell f).vertices) {s : V × V} (hs : s ∈ (D.cell f).edges)
    (has : a ∈ segment ℝ s.1 s.2) : ∃ U ∈ 𝓝 a, U ∩ D.support = U ∩ segment ℝ s.1 s.2 := by
  obtain ⟨U₀, hU₀, hU₀eq⟩ :=
    (D.cell_isSimpleArcOrLoop f).exists_nhds_inter_toSet_eq ha hav hs has
  have hend : a ∉ ({D.vertex (edgeSource f), D.vertex (edgeTarget f)} : Set V) := by
    rintro (rfl | rfl)
    · exact hav (D.cell f).first_mem_vertices
    · exact hav (D.cell f).last_mem_vertices
  have haPI : a ∈ (D.edgePath f).Interior := by
    have : a ∈ range (D.edgePath f) := by rw [D.range_edgePath f]; exact ha
    obtain ⟨t, rfl⟩ := this
    refine ⟨t, ⟨?_, ?_⟩, rfl⟩
    · exact lt_of_le_of_ne t.2.1 fun h0 ↦ hend (by simp [← h0])
    · exact lt_of_le_of_ne t.2.2 fun h1 ↦ hend (by simp [h1])
  have ha_not_vertex : a ∉ range D.vertex :=
    (D.pathInterior_edgePath_disjoint_vertex f).notMem_of_mem_left haPI
  have ha_not_other {e : E(G)} (he : e ≠ f) : a ∉ (D.cell e).toSet := by
    intro hae
    obtain ⟨t, rfl⟩ := D.range_edgePath e ▸ hae
    obtain rfl | h0 := eq_or_ne t 0
    · exact ha_not_vertex ⟨_, Path.source .. |>.symm⟩
    obtain rfl | h1 := eq_or_ne t 1
    · exact ha_not_vertex ⟨_, Path.target .. |>.symm⟩
    exact (D.pathInterior_edgePath_disjoint he.symm).notMem_of_mem_left haPI
      ⟨t, ⟨lt_of_le_of_ne t.2.1 h0.symm, lt_of_le_of_ne t.2.2 h1⟩, rfl⟩
  have hcellCompact (e : E(G)) : IsCompact (D.cell e).toSet := by
    rw [PolygonalPath.toSet_eq_insert_biUnion]
    exact isCompact_singleton.union <|
      ((D.cell e).edges.finite_toSet).isCompact_biUnion fun _ _ ↦ isCompact_segment _ _
  let K : Set V := range D.vertex ∪ ⋃ e ∈ {e : E(G) | e ≠ f}, (D.cell e).toSet
  have hK : IsClosed K := (Set.finite_range D.vertex).isCompact.isClosed.union
      ((Set.toFinite _).isCompact_biUnion fun e _ ↦ hcellCompact e).isClosed
  have haK : a ∉ K := by
    refine not_or.mpr ⟨ha_not_vertex, fun ha' ↦ ?_⟩
    obtain ⟨e, he, hae⟩ := mem_iUnion₂.mp ha'
    exact ha_not_other he hae
  refine ⟨U₀ ∩ Kᶜ, Filter.inter_mem hU₀ (hK.isOpen_compl.mem_nhds haK), ?_⟩
  ext x
  refine ⟨fun ⟨⟨hxU₀, hxK⟩, hxsup⟩ ↦ ?_, fun ⟨hxU, hxs⟩ ↦ ⟨hxU, D.edgePath_range_subset_support f
    <| D.range_edgePath f ▸ (D.cell f).segment_subset_toSet hs hxs⟩⟩
  obtain hxsup | hxsup := D.support_eq ▸ hxsup
  · exact (hxK (Or.inl hxsup)).elim
  obtain ⟨e, he⟩ := mem_iUnion.mp hxsup
  rw [D.range_edgePath e] at he
  obtain rfl | hef := eq_or_ne e f
  · exact ⟨⟨hxU₀, hxK⟩, (hU₀eq ▸ show x ∈ U₀ ∩ (D.cell e).toSet from ⟨hxU₀, he⟩).2⟩
  exact (hxK (Or.inr (mem_iUnion₂.mpr ⟨e, hef, he⟩))).elim


variable [ContinuousAdd V]

/-! ### Building a polygonal drawing from cells

The lemmas below translate `toSet`-level disjointness into the `Path.Interior` conditions required
by `Drawing.ofVertexAndEdgePaths`. `PLDrawing.ofCells` then packages vertex positions and cells
into a drawing. -/

/-- The interior of the parametrized cell is its image minus its endpoints — for a loop, minus the
single base point, which is again the open cell. -/
theorem Path.interior_toPath {x y : V} {P : PolygonalPath x y} (h : P.IsSimpleArcOrLoop) :
    P.toPath.Interior = P.toSet \ {x, y} :=
  h.toSet_diff_endpoints.symm

theorem Path.interior_toPath_range {x y : V} {P : PolygonalPath x y} {S : Set V}
    (h : P.IsSimpleArcOrLoop) (hdisj : Disjoint (P.toSet \ {x, y}) S) :
    Disjoint (P.toPath.Interior) S :=
  (Path.interior_toPath h) ▸ hdisj

theorem Path.interior_toPath_disjoint {x y x' y' : V} {P : PolygonalPath x y}
    {Q : PolygonalPath x' y'} (hP : P.IsSimpleArcOrLoop) (hQ : Q.IsSimpleArcOrLoop)
    (hdisj : Disjoint (P.toSet \ {x, y}) (Q.toSet \ {x', y'})) :
    Disjoint (P.toPath.Interior) (Q.toPath.Interior) :=
  (Path.interior_toPath hP) ▸ (Path.interior_toPath hQ) ▸ hdisj

/-- Build a polygonal drawing from vertex positions and cells. The hypotheses are the polygonal form
of the conditions in `Drawing.ofVertexAndEdgePaths`: injectivity of each cell is replaced by
`IsSimpleArcOrLoop`, which is combinatorial, and the interior of a cell is `toSet` minus its
endpoints, which is the open cell for a loop as well as for a non-loop. -/
noncomputable def PLDrawing.ofCells (vertex : V(G) → V) (vertex_injective : Injective vertex)
    (cell : ∀ e : E(G), PolygonalPath (vertex (edgeSource e)) (vertex (edgeTarget e)))
    (cell_isSimpleArcOrLoop : ∀ e, (cell e).IsSimpleArcOrLoop)
    (cell_inter_vertex : ∀ e, Disjoint
      ((cell e).toSet \ {vertex (edgeSource e), vertex (edgeTarget e)}) (range vertex))
    (cell_inter : ∀ e f, e ≠ f → Disjoint
      ((cell e).toSet \ {vertex (edgeSource e), vertex (edgeTarget e)})
      ((cell f).toSet \ {vertex (edgeSource f), vertex (edgeTarget f)})) :
    PLDrawing G V where
  toDrawing := Drawing.ofVertexAndEdgePaths vertex vertex_injective (fun e ↦ (cell e).toPath)
    (fun e ↦ (cell_isSimpleArcOrLoop e).injOn_toPath_Ioo)
    (fun e ↦ Path.interior_toPath_range (cell_isSimpleArcOrLoop e) (cell_inter_vertex e))
    (fun e f hef ↦ Path.interior_toPath_disjoint (cell_isSimpleArcOrLoop e)
      (cell_isSimpleArcOrLoop f) (cell_inter e f hef))
  cell := cell
  cell_isSimpleArcOrLoop := cell_isSimpleArcOrLoop
  range_edgePath := fun e ↦ (cell e).toSet_eq_range_toPath.symm

@[simp]
lemma PLDrawing.ofCells_vertex {vertex : V(G) → V} {hv : Injective vertex}
    {cell : ∀ e : E(G), PolygonalPath (vertex (edgeSource e)) (vertex (edgeTarget e))}
    {hc : ∀ e, (cell e).IsSimpleArcOrLoop} {hcv : ∀ e, Disjoint
      ((cell e).toSet \ {vertex (edgeSource e), vertex (edgeTarget e)}) (range vertex)}
    {hcc : ∀ e f, e ≠ f → Disjoint
      ((cell e).toSet \ {vertex (edgeSource e), vertex (edgeTarget e)})
      ((cell f).toSet \ {vertex (edgeSource f), vertex (edgeTarget f)})} (x : V(G)) :
    (PLDrawing.ofCells vertex hv cell hc hcv hcc).vertex x = vertex x := rfl

namespace Drawing

/-- A drawing is polygonal exactly when it underlies a polygonal drawing. -/
theorem isPL_iff_exists_plDrawing (D : Drawing G V) :
    D.IsPL ↔ ∃ Q : PLDrawing G V, Q.toDrawing = D := by
  refine ⟨fun hD ↦ ?_, ?_⟩
  · choose cell hcell using hD
    exact ⟨⟨D, cell, fun e ↦ (hcell e).1, fun e ↦ (hcell e).2⟩, rfl⟩
  rintro ⟨Q, rfl⟩
  exact Q.isPL

alias ⟨IsPL.exists_plDrawing, _⟩ := isPL_iff_exists_plDrawing

/-- Restricting a polygonal drawing to a subgraph keeps it polygonal. Via
`PLDrawing.restrict`, whose cells are those of `D` retyped by `PolygonalPath.cast`. -/
theorem IsPL.restrict {D : Drawing G V} (hD : D.IsPL) (h : H ≤ G) : (D.restrict h).IsPL := by
  rw [isPL_iff_exists_plDrawing] at hD ⊢
  obtain ⟨Q, rfl⟩ := hD
  exact ⟨Q.restrict h, rfl⟩

end Drawing

/-! ### PL planarity -/

/-- A graph is PL planar if it has a polygonal drawing in the Euclidean plane. -/
def PLPlanar (G : Graph α β) : Prop := Nonempty (PLDrawing G (EuclideanSpace ℝ (Fin 2)))

theorem plPlanar_iff_exists_isPL :
    G.PLPlanar ↔ ∃ D : Drawing G (EuclideanSpace ℝ (Fin 2)), D.IsPL := by
  refine ⟨fun ⟨Q⟩ ↦ ⟨Q.toDrawing, Q.isPL⟩, fun ⟨D, hD⟩ ↦ ?_⟩
  obtain ⟨Q, rfl⟩ := hD.exists_plDrawing
  exact ⟨Q⟩

theorem PLPlanar.planar (hG : G.PLPlanar) : G.Planar :=
  ⟨hG.some.toDrawing⟩

end

end Graph
