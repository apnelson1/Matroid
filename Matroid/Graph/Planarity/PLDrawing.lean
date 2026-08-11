import Matroid.Graph.Planarity.Drawing
import Matroid.ForMathlib.Geometry.PolygonalPath.SimpleArcOrLoop

/-!
# Polygonal drawings

A drawing is *polygonal*, or *PL*, when the image of every edge is a finite union of segments. This
file gives that notion two forms — the data `Graph.PLDrawing`, which carries the polygonal path
realising each edge, and the proposition `Graph.Drawing.IsPL`, which asserts one exists — and states
the reduction of planarity to PL planarity.

Everything is stated over a real topological vector space rather than the plane: `PolygonalPath`
needs exactly `AddCommGroup`, `Module ℝ`, `TopologicalSpace`, `ContinuousAdd` and `ContinuousSMul`,
and no statement here needs more. The plane and the sphere enter only in the plane-topology files:
PL structure lives in `ℝ²`, faces are taken in `OnePoint ℝ²` after `Drawing.postcomp`, and no PL
structure is ever put on the sphere.

## Implementation notes

The conditions constrain the *image* `Set.range (D.edgePath e)` of each edge — Status.md's closed
cell `Γ_e` — and never the parametrisation. Requiring `D.edgePath e = (cell e).toPath` would pin a
traversal speed carrying no mathematical content: `PolygonalPath.toPath` traverses at dyadic speeds
while `Realization.edgePath` is affine, so every re-cutting or concatenation of a cell would carry a
renormalisation obligation. Nothing is lost, since a drawing restricted to a closed edge is an
embedding of `I`, so image equality already determines the parametrisation up to a homeomorphism of
`I` fixing the endpoints.

Loops are allowed: for a loop `edgeSource e = edgeTarget e`, and the cell is a closed polygonal
path. The arc/loop case split is confined to `PolygonalPath.IsSimpleArcOrLoop` and discharged by
`PolygonalPath.IsSimpleArcOrLoop.existsUnique_edge`; Mathlib's `Polygon` is reachable through
`PolygonalPath.toPolygon` and never appears here.

`cell_isSimpleArcOrLoop` is not implied by the other fields — a path traversing the same segments
twice has the same image — and is what makes the `edges` list of a cell a faithful description of
it. It is the hypothesis the local structure lemma consumes.

## Main definitions

* `Graph.PLDrawing` : a drawing together with a polygonal path realising each edge.
* `Graph.Drawing.IsPL` : the drawing is polygonal.
* `Graph.PLPlanar` : the graph has a polygonal drawing in the plane.

## Main statements

* `Graph.exists_plDrawing_of_cells` : build a polygonal drawing from vertex positions and cells.
* `Graph.Drawing.IsPL.restrict` : a subgraph of a polygonal drawing is polygonally drawn.
* `Graph.PLDrawing.exists_nhds_inter_support_eq_segment` : Status.md 3.6, the edge-interior case.

The reduction `Planar ↔ PLPlanar` is in `Matroid.Graph.Planarity.PLReduction`, which is where the
approximation lemmas are imported; this file deliberately does not depend on them.
-/

open Function Set Topology

namespace Graph

noncomputable section

universe u

variable {α β : Type*} {G H : Graph α β} {e : β} {u v : α}
variable {V : Type u} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [ContinuousSMul ℝ V]
  [ContinuousAdd V]

/-- A polygonal drawing of `G` in `V`: a drawing together with, for each edge, a polygonal path
whose image is the closed cell of that edge. -/
structure PLDrawing (G : Graph α β) (V : Type u) [AddCommGroup V] [Module ℝ V]
    [TopologicalSpace V] [ContinuousSMul ℝ V] [ContinuousAdd V] extends Drawing G V where
  /-- The polygonal path realising the edge `e`. -/
  cell : ∀ e : E(G), PolygonalPath (toDrawing.vertex (edgeSource e))
    (toDrawing.vertex (edgeTarget e))
  /-- Each cell is an embedded arc, or an embedded circle when the edge is a loop. -/
  cell_isSimpleArcOrLoop : ∀ e, (cell e).IsSimpleArcOrLoop
  /-- Each cell traces out exactly the closed cell of its edge. -/
  range_edgePath : ∀ e, range (toDrawing.edgePath e) = (cell e).toSet

/-- A drawing is polygonal when every closed cell is the image of an embedded polygonal arc or
circle. The witnesses are not canonical — subdivision, reversal and the orientation of the edge all
change them — so they are existentially quantified here and carried by `PLDrawing` where a
construction needs them. -/
def Drawing.IsPL (D : Drawing G V) : Prop :=
  ∀ e : E(G), ∃ P : PolygonalPath (D.vertex (edgeSource e)) (D.vertex (edgeTarget e)),
    P.IsSimpleArcOrLoop ∧ range (D.edgePath e) = P.toSet

namespace PLDrawing

variable {D : PLDrawing G V}

lemma isPL (D : PLDrawing G V) : D.toDrawing.IsPL :=
  fun e ↦ ⟨D.cell e, D.cell_isSimpleArcOrLoop e, D.range_edgePath e⟩

/-- Restrict a polygonal drawing to a subgraph. The cells transport unchanged: a subgraph has the
same ends for each of its edges, and the orientation of an edge is determined by its ends — `ArbRel`
fixes one linear order per *type*, so `IsSubgraph.source` and `IsSubgraph.target` hold — so all that
is needed is the propositional retyping of the endpoints, `PolygonalPath.cast`. No reversal. -/
def restrictCell (D : PLDrawing G V) (h : H ≤ G) (e : E(H)) :
    PolygonalPath ((D.toDrawing.restrict h).vertex (edgeSource e))
      ((D.toDrawing.restrict h).vertex (edgeTarget e)) :=
  (D.cell ⟨e.1, edgeSet_mono h e.2⟩).cast
    (D.toDrawing.restrict_vertex_edgeSource h e).symm
    (D.toDrawing.restrict_vertex_edgeTarget h e).symm

theorem isSimpleArcOrLoop_restrictCell (D : PLDrawing G V) (h : H ≤ G) (e : E(H)) :
    (D.restrictCell h e).IsSimpleArcOrLoop := by
  rw [restrictCell]
  exact (PolygonalPath.isSimpleArcOrLoop_cast _ _).mpr
    (D.cell_isSimpleArcOrLoop ⟨e.1, edgeSet_mono h e.2⟩)

theorem range_edgePath_restrictCell (D : PLDrawing G V) (h : H ≤ G) (e : E(H)) :
    range ((D.toDrawing.restrict h).edgePath e) = (D.restrictCell h e).toSet := by
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
with the vertex images. Status.md's support-level description of a polygonal drawing, which is a
consequence of the definition rather than a workable replacement for it: it forgets which segments
belong to which edge. -/
theorem exists_finite_support [G.Finite] (D : PLDrawing G V) :
    ∃ S : Set (V × V), S.Finite ∧
      D.toDrawing.support = range D.toDrawing.vertex ∪ ⋃ s ∈ S, segment ℝ s.1 s.2 := by
  let S : Set (V × V) := ⋃ e : E(G), {s | s ∈ (D.cell e).edges}
  refine ⟨S, ?_, ?_⟩
  · have : Finite (E(G)) := inferInstance
    exact finite_iUnion fun e ↦ (D.cell e).edges.finite_toSet
  · rw [Drawing.support_eq]
    refine subset_antisymm ?_ ?_
    · intro x hx
      obtain hx | hx := hx
      · exact Or.inl hx
      · obtain ⟨e, he⟩ := mem_iUnion.mp hx
        have hx' : x ∈ (D.cell e).toSet := by rwa [← D.range_edgePath e]
        rw [PolygonalPath.toSet_eq_insert_biUnion] at hx'
        obtain hx' | hx' := mem_insert_iff.mp hx'
        · exact Or.inl ⟨edgeTarget e, hx'.symm⟩
        · obtain ⟨s, hs, hseg⟩ := mem_iUnion₂.mp hx'
          exact Or.inr <| mem_iUnion₂.mpr ⟨s, mem_iUnion.mpr ⟨e, hs⟩, hseg⟩
    · intro x hx
      obtain hx | hx := hx
      · exact Or.inl hx
      · obtain ⟨s, hsS, hseg⟩ := mem_iUnion₂.mp hx
        obtain ⟨e, hs⟩ := mem_iUnion.mp hsS
        refine Or.inr <| mem_iUnion.mpr ⟨e, ?_⟩
        rw [D.range_edgePath e, PolygonalPath.toSet_eq_insert_biUnion]
        exact mem_insert_of_mem _ (mem_iUnion₂.mpr ⟨s, hs, hseg⟩)

/-- Status.md 3.6, edge-interior case: near a point interior to one cell, the whole drawing looks
like the single segment of that cell through the point. The vertex case, where the segments of
every edge at a vertex meet, is stated with the star lemma in the plane-topology development. -/
theorem exists_nhds_inter_support_eq_segment [G.Finite] [T2Space V] [IsTopologicalAddGroup V]
    (D : PLDrawing G V) {f : E(G)} {a : V} (ha : a ∈ (D.cell f).toSet)
    (hav : a ∉ (D.cell f).vertices) {s : V × V} (hs : s ∈ (D.cell f).edges)
    (has : a ∈ segment ℝ s.1 s.2) :
    ∃ U ∈ 𝓝 a, U ∩ D.toDrawing.support = U ∩ segment ℝ s.1 s.2 := by
  obtain ⟨U₀, hU₀, hU₀eq⟩ :=
    (D.cell_isSimpleArcOrLoop f).exists_nhds_inter_toSet_eq ha hav hs has
  have hend :
      a ∉ ({D.toDrawing.vertex (edgeSource f), D.toDrawing.vertex (edgeTarget f)} : Set V) := by
    intro h
    refine hav ?_
    simp only [mem_insert_iff, mem_singleton_iff] at h
    obtain rfl | rfl := h
    · exact (D.cell f).first_mem_vertices
    · exact (D.cell f).last_mem_vertices
  have haPI : a ∈ Drawing.pathInterior (D.toDrawing.edgePath f) := by
    have : a ∈ range (D.toDrawing.edgePath f) := by rw [D.range_edgePath f]; exact ha
    obtain ⟨t, rfl⟩ := this
    refine ⟨t, ⟨?_, ?_⟩, rfl⟩
    · exact lt_of_le_of_ne t.2.1 fun h0 ↦ hend (by simp [← h0])
    · exact lt_of_le_of_ne t.2.2 fun h1 ↦ hend (by simp [h1])
  have ha_not_vertex : a ∉ range D.toDrawing.vertex :=
    (Drawing.pathInterior_edgePath_disjoint_vertex D.toDrawing f).notMem_of_mem_left haPI
  have ha_not_other {e : E(G)} (he : e ≠ f) : a ∉ (D.cell e).toSet := by
    intro hae
    rw [← D.range_edgePath e] at hae
    obtain ⟨t, rfl⟩ := hae
    by_cases h0 : t = 0
    · refine ha_not_vertex ?_
      rw [h0, Path.source]; exact ⟨_, rfl⟩
    by_cases h1 : t = 1
    · refine ha_not_vertex ?_
      rw [h1, Path.target]; exact ⟨_, rfl⟩
    · exact (Drawing.pathInterior_edgePath_disjoint D.toDrawing he.symm).notMem_of_mem_left haPI
        ⟨t, ⟨lt_of_le_of_ne t.2.1 (Ne.symm h0), lt_of_le_of_ne t.2.2 h1⟩, rfl⟩
  have hcellCompact (e : E(G)) : IsCompact (D.cell e).toSet := by
    rw [PolygonalPath.toSet_eq_insert_biUnion]
    exact isCompact_singleton.union <|
      ((D.cell e).edges.finite_toSet).isCompact_biUnion fun _ _ ↦ isCompact_segment _ _
  let K : Set V := range D.toDrawing.vertex ∪ ⋃ e ∈ {e : E(G) | e ≠ f}, (D.cell e).toSet
  have hK : IsClosed K := by
    refine IsClosed.union ?_ ?_
    · have : Finite V(G) := inferInstance
      exact (Set.finite_range D.toDrawing.vertex).isCompact.isClosed
    · exact ((Set.toFinite _).isCompact_biUnion fun e _ ↦ hcellCompact e).isClosed
  have haK : a ∉ K := by
    refine not_or.mpr ⟨ha_not_vertex, ?_⟩
    intro ha'
    obtain ⟨e, he, hae⟩ := mem_iUnion₂.mp ha'
    exact ha_not_other he hae
  refine ⟨U₀ ∩ Kᶜ, Filter.inter_mem hU₀ (hK.isOpen_compl.mem_nhds haK), ?_⟩
  ext x
  constructor
  · rintro ⟨⟨hxU₀, hxK⟩, hxsup⟩
    rw [Drawing.support_eq] at hxsup
    obtain hxsup | hxsup := hxsup
    · exact (hxK (Or.inl hxsup)).elim
    · obtain ⟨e, he⟩ := mem_iUnion.mp hxsup
      rw [D.range_edgePath e] at he
      by_cases hef : e = f
      · subst hef
        have : x ∈ U₀ ∩ (D.cell e).toSet := ⟨hxU₀, he⟩
        rw [hU₀eq] at this
        exact ⟨⟨hxU₀, hxK⟩, this.2⟩
      · exact (hxK (Or.inr (mem_iUnion₂.mpr ⟨e, hef, he⟩))).elim
  · rintro ⟨hxU, hxs⟩
    refine ⟨hxU, Drawing.edgePath_range_subset_support D.toDrawing f ?_⟩
    rw [D.range_edgePath f]
    exact (D.cell f).segment_subset_toSet hs hxs


end PLDrawing

/-! ### Building a polygonal drawing from cells

The two translation theorems below turn the `toSet`-level hypotheses a caller can check
combinatorially into the `pathInterior`-level hypotheses `Drawing.ofVertexAndEdgePaths` demands.
They are the reason `PLDrawing.ofCells` is a definition rather than an existence statement: all the
analysis lives here, and §2.6 and §6 verify their obligations on `toSet`s. -/

/-- The interior of the parametrized cell is its image minus its endpoints — for a loop, minus the
single base point, which is again the open cell. -/
theorem pathInterior_toPath {x y : V} {P : PolygonalPath x y} (h : P.IsSimpleArcOrLoop) :
    Drawing.pathInterior P.toPath = P.toSet \ {x, y} :=
  h.toSet_diff_endpoints.symm

theorem disjoint_pathInterior_toPath_range {x y : V} {P : PolygonalPath x y} {S : Set V}
    (h : P.IsSimpleArcOrLoop) (hdisj : Disjoint (P.toSet \ {x, y}) S) :
    Disjoint (Drawing.pathInterior P.toPath) S :=
  (pathInterior_toPath h) ▸ hdisj

theorem disjoint_pathInterior_toPath {x y x' y' : V} {P : PolygonalPath x y}
    {Q : PolygonalPath x' y'} (hP : P.IsSimpleArcOrLoop) (hQ : Q.IsSimpleArcOrLoop)
    (hdisj : Disjoint (P.toSet \ {x, y}) (Q.toSet \ {x', y'})) :
    Disjoint (Drawing.pathInterior P.toPath) (Drawing.pathInterior Q.toPath) :=
  (pathInterior_toPath hP) ▸ (pathInterior_toPath hQ) ▸ hdisj

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
    (fun e ↦ disjoint_pathInterior_toPath_range (cell_isSimpleArcOrLoop e) (cell_inter_vertex e))
    (fun e f hef ↦ disjoint_pathInterior_toPath (cell_isSimpleArcOrLoop e)
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
    (PLDrawing.ofCells vertex hv cell hc hcv hcc).toDrawing.vertex x = vertex x := rfl

namespace Drawing

/-- A drawing is polygonal exactly when it underlies a polygonal drawing. -/
theorem isPL_iff_exists_plDrawing (D : Drawing G V) :
    D.IsPL ↔ ∃ Q : PLDrawing G V, Q.toDrawing = D := by
  constructor
  · intro hD
    choose cell hcell using hD
    exact ⟨⟨D, cell, fun e ↦ (hcell e).1, fun e ↦ (hcell e).2⟩, rfl⟩
  · rintro ⟨Q, rfl⟩
    exact Q.isPL

/-- Restricting a polygonal drawing to a subgraph keeps it polygonal. Via
`PLDrawing.restrict`, whose cells are those of `D` retyped by `PolygonalPath.cast`. -/
theorem IsPL.restrict {D : Drawing G V} (hD : D.IsPL) (h : H ≤ G) : (D.restrict h).IsPL := by
  rw [isPL_iff_exists_plDrawing] at hD ⊢
  obtain ⟨Q, rfl⟩ := hD
  exact ⟨Q.restrict h, rfl⟩

end Drawing

/-! ### PL planarity -/

/-- A graph is PL planar if it has a polygonal drawing in the Euclidean plane. The converse
implication `Planar → PLPlanar`, Status.md 2.6, is in `Matroid.Graph.Planarity.PLReduction`. -/
def PLPlanar (G : Graph α β) : Prop :=
  Nonempty (PLDrawing G (EuclideanSpace ℝ (Fin 2)))

theorem plPlanar_iff_exists_isPL :
    G.PLPlanar ↔ ∃ D : Drawing G (EuclideanSpace ℝ (Fin 2)), D.IsPL := by
  constructor
  · rintro ⟨Q⟩
    exact ⟨Q.toDrawing, Q.isPL⟩
  · rintro ⟨D, hD⟩
    rw [Drawing.isPL_iff_exists_plDrawing] at hD
    obtain ⟨Q, rfl⟩ := hD
    exact ⟨Q⟩

theorem PLPlanar.planar (hG : G.PLPlanar) : G.Planar :=
  ⟨hG.some.toDrawing⟩

end

end Graph
