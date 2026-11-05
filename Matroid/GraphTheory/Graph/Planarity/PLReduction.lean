module

public import Matroid.Graph.Planarity.PLDrawing
public import Matroid.ForMathlib.Geometry.PrimitiveLinkReplacement

/-!
# Polygonal replacement of finite graph drawings

A drawing of a finite graph in a real normed space admits a polygonal drawing with the
same vertex positions. The simultaneous replacement theorem for primitive-link families supplies
the cells; the drawing hypotheses verify its endpoint incidence conditions, and
`PLDrawing.ofCells` assembles the result.
-/

open Function Set Topology Metric PolygonalPath

namespace Graph

public noncomputable section

variable {α β V : Type*} {G : Graph α β} [NormedAddCommGroup V]

/-- Replace a drawing of a finite graph in a real normed space by a polygonal drawing with
the same vertex positions. -/
theorem Drawing.exists_plDrawing [G.Finite] [NormedSpace ℝ V] (D : Drawing G V) :
    ∃ Q : PLDrawing G V, ∀ x, Q.vertex x = D.vertex x := by
  let Z := range D.vertex
  let a (e : E(G)) : Z := ⟨D.vertex (edgeSource e), mem_range_self _⟩
  let b (e : E(G)) : Z := ⟨D.vertex (edgeTarget e), mem_range_self _⟩
  have : Finite Z := (finite_range D.vertex).to_subtype
  have hFV (e : E(G)) : range (D.edgePath e) ∩ Z ⊆ {(a e).1, (b e).1} := by
    rintro w ⟨hw, hwZ⟩
    obtain h | h | h := (D.edgePath e).mem_range_iff_mem_interior_or_source_or_target w |>.mp hw
    · exact Or.inl h
    · exact Or.inr h
    · exact ((D.pathInterior_edgePath_disjoint_vertex e).notMem_of_mem_left h hwZ).elim
  have hFF : Pairwise fun e f ↦ range (D.edgePath e) ∩ range (D.edgePath f) ⊆ Z := by
    intro e f hef w hw
    have hw' := ((D.range_edgePath_inter hef).subset hw).1
    rcases hw' with rfl | rfl <;> exact mem_range_self _
  obtain ⟨L, hL, hpoly, hV, hcell, -⟩ := exists_polygonal_primitiveLink_family
    (a := a) (b := b) (fun e ↦ (D.edgePath_isPrimitive e).isPrimitiveLink)
    hFV hFF (fun _ ↦ univ) (fun _ ↦ isOpen_univ) (fun _ ↦ subset_univ _)
  choose cell hprimitive hrange using fun e ↦ (hL e).exists_polygonalPath (hpoly e)
  have hcv (e : E(G)) : Disjoint ((cell e).toSet \
      {D.vertex (edgeSource e), D.vertex (edgeTarget e)}) (range D.vertex) := by
    exact disjoint_left.mpr fun w hw hwZ ↦ hw.2 ((hV e).subset ⟨hrange e ▸ hw.1, hwZ⟩)
  have hcc (e f : E(G)) (hef : e ≠ f) : Disjoint
      ((cell e).toSet \ {D.vertex (edgeSource e), D.vertex (edgeTarget e)})
      ((cell f).toSet \ {D.vertex (edgeSource f), D.vertex (edgeTarget f)}) := by
    exact disjoint_left.mpr fun w hw hw' ↦
      hw.2 ((hV e).subset ⟨hrange e ▸ hw.1,
        hcell hef ⟨hrange e ▸ hw.1, hrange f ▸ hw'.1⟩⟩)
  exact ⟨PLDrawing.ofCells D.vertex D.vertex_injective cell hprimitive hcv hcc, fun _ ↦ rfl⟩

/-- A planar finite graph has a polygonal plane drawing. -/
theorem Planar.plPlanar [G.Finite] (hG : G.Planar) : G.PLPlanar :=
  ⟨hG.some.exists_plDrawing.choose⟩

/-- Planarity and polygonal planarity are equivalent for finite graphs. -/
theorem planar_iff_plPlanar [G.Finite] : G.Planar ↔ G.PLPlanar :=
  ⟨Planar.plPlanar, PLPlanar.planar⟩

end

end Graph
