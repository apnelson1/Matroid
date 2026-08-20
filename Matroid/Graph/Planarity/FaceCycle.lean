module

public import Matroid.ForMathlib.Geometry.Polygon.Crosscut
public import Matroid.Graph.Connected.Ear
public import Matroid.Graph.Planarity.Face
public import Matroid.Graph.Planarity.PLDrawing

/-!
# Faces of a 2-connected polygonal drawing are bounded by cycles

In a polygonal drawing of a finite loopless `2`-connected graph, every face has a cycle of the
graph as its frontier, and is a whole component of the complement of that cycle.

The main theorem assumes only finiteness, looplessness, and 2-connectivity. The cycle bounding a
face may be a digon, so the conclusion does not require three distinct cycle vertices; the initial
cycle used for ear induction has the stronger size bound supplied by `ConnGE.exists_isCycle_le`.

## Proof of the main theorem, in the steps the statement is built to support

Write `D|H` for `D.restrict`, `|H|` for `(D|H).support` and `𝕊` for `OnePoint V`, the sphere over
the plane `V`.

1. **Base cycle.** `ConnGE.exists_isCycle_le` (`Forest.lean`) gives `C₀ ≤ G` with `C₀.IsCycle` and
   `3 ≤ V(C₀).encard`.
2. **Induction.** `ConnGE.ear_induction` over `C₀ ≤ H ≤ G`, with motive
   `fun H ↦ ∀ hle : H ≤ G, ∀ F : (D|hle).onePoint.Face, <conclusion for F>`.
3. **Base case `H = C₀`.** `exists_isSimpleLoop_toSet_eq_support_of_isCyclicWalk` below traces
   `|C₀|` as a simple polygonal loop; `IsSimpleLoop.isJordanCurve` and
   `IsSimpleLoop.exists_sides_onePoint` (`Geometry/Polygon/JordanCurve.lean:39,51`) split `𝕊 ∖ |C₀|`
   into two open connected sets, each with frontier `|C₀|`. Both are faces by
   `Drawing.exists_faceSet_eq` (`Face.lean:162`), and they exhaust the complement, so the given `F`
   is one of them and its cycle is `C₀`.
4. **Step.** Attach an ear `P` to `H`, giving `H' := H ∪ P.toGraph` and `H' ≤ G` by
   `IsEar.union_le` (`Ear.lean:105`). The relative interior of `|P|` is connected and misses `|H|`,
   so it lies in a single face `F'` of `D|H`, and the two ends of `P` lie in `frontier F'`.
5. **Cut that face.** The induction hypothesis gives `frontier F' = |C|` for a cycle `C ≤ H`.
   The ends of `P` are vertex images on `|C|`, hence images of *vertices* of `C`
   (`Drawing.pathInterior_edgePath_disjoint_vertex` `Drawing.lean:157` says no open cell contains a
   vertex image, and `Drawing.vertex_injective` `Drawing.lean:129` identifies which vertex). They
   are distinct, so they split `C` into two paths `C₁, C₂`. Now
   `exists_two_regions_crosscut` (`ThetaCurve.lean:132`) with `J := |C|`, `F := F'`, `A := |P|`
   cuts `F'` into exactly two regions, with frontiers `|C₁ + P|` and `|C₂ + P|`. Its hypothesis
   that `A` meets `J` in exactly its two ends is
   `Drawing.support_restrict_inter_support_restrict_of_isEar` below — the one hypothesis of 3.10
   that has to come from the drawing axioms rather than from a caller.
6. **Every other face is untouched.** A face `F'' ≠ F'` of `D|H` misses `|H'|`, so it is still a
   face of `D|H'`; conversely `|H| ⊆ |H'|` puts every face of `D|H'` inside a face of `D|H`. So the
   faces of `D|H'` are the `F'' ≠ F'` together with the two pieces of `F' ∖ |P|`, and each has the
   required cycle — `C₁ + P` and `C₂ + P` are cycles by `IsCyclicWalk.toGraph_isCycle`
   (`Forest.lean:192`).
7. **Termination** is inside `ear_induction`, not here.

## Main statements

* `Graph.Drawing.support_restrict_inter_support_restrict_of_isEar` : an ear meets the rest of the
  drawing exactly at its two ends. Needs no polygonality.
* `Graph.PLDrawing.exists_polygonalPath_toSet_eq_support_of_isPath` : a polygonal drawing of a path
  traces a simple polygonal arc.
* `Graph.PLDrawing.exists_isSimpleLoop_toSet_eq_support_of_isCyclicWalk` : and of a cyclic walk, a
  simple polygonal loop.
* `Graph.PLDrawing.exists_polygon_isSimple_of_isCycle` : the `Polygon` form of the latter, which is
  what `exists_two_regions_crosscut` consumes.
* `Graph.PLDrawing.exists_isCycle_frontier_faceSet_eq` : the face-cycle theorem.
* `Graph.PLDrawing.exists_isCycle_isFacialSubgraph` : the same result in `IsFacialSubgraph` form.
-/

open Function Set Topology
open scoped unitInterval

namespace Graph

public noncomputable section

variable {α β V : Type*} {G H C : Graph α β} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace Drawing

section Ear

variable {X : Type*} [TopologicalSpace X]

/- **Route.** `⊇` is immediate: `hP.first_mem` and `hP.last_mem` put both ends in `V(H)`, and
`Drawing.vertex_mem_support` (`Drawing.lean:120`) puts their images in both supports.

`⊆` is where the drawing axioms are spent. Expand both sides with `Drawing.support_eq`
(`Drawing.lean:137`) — a support is the union of the closed cells and the vertex images — and take
a point `z` in both. Four cases, each closed by one lemma:

* `z` a vertex image on each side. `Drawing.vertex_injective` (`Drawing.lean:129`) makes it one
  vertex of `V(P.toGraph) ∩ V(H)`, which `hP.internal_disjoint` cuts down to `{P.first, P.last}`
  (`WList.mem_vertexSet_iff` splits a walk's vertices into its ends and `internalVertexSet`).
* `z` interior to a cell of `P` and a vertex image of `H`, or the mirror case:
  `Drawing.pathInterior_edgePath_disjoint_vertex` (`Drawing.lean:157`) — no open cell contains any
  vertex image — rules both out outright.
* `z` interior to a cell of each. `hP.edge_disjoint` makes the two edges distinct, so
  `Drawing.range_edgePath_inter` (`Drawing.lean:171`) confines `z` to the images of shared ends,
  which are vertex images, contradicting the previous case.

`Drawing.range_edgePath_restrict` (`Drawing.lean:416`) is what identifies a restricted cell with
the corresponding cell of `D` in each case, and `Drawing.restrict_vertex` (`Drawing.lean:397`) does
the same for vertex images. Nothing here is polygonal, finite, or planar. -/
/-- **An ear meets the rest of the drawing exactly at its two ends.**

This is the hypothesis `exists_two_regions_crosscut` calls `hAJ`, and the only
one of its hypotheses that the drawing axioms have to produce rather than a caller. It is stated
against `H` rather than against the facial cycle `C ≤ H` because that is the stronger statement and
the one whose proof is the drawing axioms; the `C` version follows by intersecting, since both ends
lie on `|C|`.

Costs nothing beyond `Drawing`: no polygonality, no finiteness, no plane. -/
theorem support_restrict_inter_support_restrict_of_isEar (D : Drawing G X) {P : WList α β}
    (hP : G.IsEar H P) (hle : H ≤ G) :
    (D.restrict hP.isPath.isWalk.toGraph_le).support ∩ (D.restrict hle).support =
      {D.vertex ⟨P.first, hP.isPath.isWalk.first_mem⟩,
        D.vertex ⟨P.last, hP.isPath.isWalk.last_mem⟩} := by
  let hPG := hP.isPath.isWalk.toGraph_le
  have hedge {K : Graph α β} (hK : K ≤ G) (e : E(K)) (t : I) :
      (D.restrict hK).edgePath e t = D.edgePath ⟨e.1, edgeSet_mono hK e.2⟩ t := by
    rw [edgePath_apply, edgePath_apply, restrict_apply, hK.RealizationEmbedding_edgePath]
  have hinterior {K : Graph α β} (hK : K ≤ G) (e : E(K)) :
      ((D.restrict hK).edgePath e).Interior =
        (D.edgePath ⟨e.1, edgeSet_mono hK e.2⟩).Interior := by
    ext z
    simp only [Path.Interior, mem_image]
    exact ⟨fun ⟨t, ht, ht'⟩ ↦ ⟨t, ht, (hedge hK e t).symm ▸ ht'⟩,
      fun ⟨t, ht, ht'⟩ ↦ ⟨t, ht, hedge hK e t ▸ ht'⟩⟩
  have hends {z : X} (hzP : z ∈ range (D.restrict hPG).vertex)
      (hzH : z ∈ range (D.restrict hle).vertex) :
      z = D.vertex ⟨P.first, hP.isPath.isWalk.first_mem⟩ ∨
        z = D.vertex ⟨P.last, hP.isPath.isWalk.last_mem⟩ := by
    obtain ⟨x, rfl⟩ := hzP
    obtain ⟨y, hy⟩ := hzH
    have hxG : x.1 ∈ V(G) := vertexSet_mono hPG x.2
    have hyG : y.1 ∈ V(G) := vertexSet_mono hle y.2
    have hxy : x.1 = y.1 := by
      have := D.vertex_injective <|
        (restrict_vertex D hPG x).symm.trans <| hy.symm.trans (restrict_vertex D hle y)
      exact Subtype.ext_iff.mp this
    have hxP : x.1 ∈ P := by
      rw [← WList.mem_vertexSet_iff, ← WList.toGraph_vertexSet]
      exact x.2
    have hxH : x.1 ∈ V(H) := hxy ▸ y.2
    obtain h1 | hint | h2 := WList.mem_iff_eq_first_or_mem_internalVertexSet_or_eq_last.mp hxP
    · refine Or.inl ?_
      rw [restrict_vertex]
      exact congrArg D.vertex (Subtype.ext h1)
    · exact (hP.internal_disjoint.notMem_of_mem_left hint hxH).elim
    · refine Or.inr ?_
      rw [restrict_vertex]
      exact congrArg D.vertex (Subtype.ext h2)
  have not_intP {z : X} (hzH : z ∈ (D.restrict hle).support) (e : E(P.toGraph)) :
      z ∉ ((D.restrict hPG).edgePath e).Interior := by
    intro hinter
    have hinterG : z ∈ (D.edgePath ⟨e.1, edgeSet_mono hPG e.2⟩).Interior := by
      rwa [← hinterior hPG e]
    rw [support_eq, mem_union] at hzH
    rcases hzH with hV | hE
    · obtain ⟨y, rfl⟩ := hV
      exact (D.pathInterior_edgePath_disjoint_vertex _).notMem_of_mem_left hinterG
        ⟨⟨y.1, vertexSet_mono hle y.2⟩, (restrict_vertex D hle y).symm⟩
    · obtain ⟨f, hf⟩ := mem_iUnion.mp hE
      rw [range_edgePath_restrict] at hf
      obtain hsrc | htgt | hinterH :=
        (D.edgePath ⟨f.1, edgeSet_mono hle f.2⟩).mem_range_iff_mem_interior_or_source_or_target z
          |>.mp hf
      · exact (D.pathInterior_edgePath_disjoint_vertex _).notMem_of_mem_left hinterG
          ⟨edgeSource _, hsrc.symm⟩
      · exact (D.pathInterior_edgePath_disjoint_vertex _).notMem_of_mem_left hinterG
          ⟨edgeTarget _, htgt.symm⟩
      · have hef : (⟨e.1, edgeSet_mono hPG e.2⟩ : E(G)) ≠ ⟨f.1, edgeSet_mono hle f.2⟩ := by
          intro h
          have heP : e.1 ∈ P.edgeSet := by
            rw [← WList.toGraph_edgeSet]
            exact e.2
          have hfH : e.1 ∈ H.edgeSet := by
            rw [Subtype.ext_iff.mp h]
            exact f.2
          exact hP.edge_disjoint.notMem_of_mem_left heP hfH
        exact (D.pathInterior_edgePath_disjoint hef).notMem_of_mem_left hinterG hinterH
  have not_intH {z : X} (hzP : z ∈ (D.restrict hPG).support) (f : E(H)) :
      z ∉ ((D.restrict hle).edgePath f).Interior := by
    intro hinter
    have hinterG : z ∈ (D.edgePath ⟨f.1, edgeSet_mono hle f.2⟩).Interior := by
      rwa [← hinterior hle f]
    rw [support_eq, mem_union] at hzP
    rcases hzP with hV | hE
    · obtain ⟨x, rfl⟩ := hV
      exact (D.pathInterior_edgePath_disjoint_vertex _).notMem_of_mem_left hinterG
        ⟨⟨x.1, vertexSet_mono hPG x.2⟩, (restrict_vertex D hPG x).symm⟩
    · obtain ⟨e, he⟩ := mem_iUnion.mp hE
      rw [range_edgePath_restrict] at he
      obtain hsrc | htgt | hinterP :=
        (D.edgePath ⟨e.1, edgeSet_mono hPG e.2⟩).mem_range_iff_mem_interior_or_source_or_target z
          |>.mp he
      · exact (D.pathInterior_edgePath_disjoint_vertex _).notMem_of_mem_left hinterG
          ⟨edgeSource _, hsrc.symm⟩
      · exact (D.pathInterior_edgePath_disjoint_vertex _).notMem_of_mem_left hinterG
          ⟨edgeTarget _, htgt.symm⟩
      · have hef : (⟨e.1, edgeSet_mono hPG e.2⟩ : E(G)) ≠ ⟨f.1, edgeSet_mono hle f.2⟩ := by
          intro h
          have heP : e.1 ∈ P.edgeSet := by
            rw [← WList.toGraph_edgeSet]
            exact e.2
          have hfH : e.1 ∈ H.edgeSet := by
            rw [Subtype.ext_iff.mp h]
            exact f.2
          exact hP.edge_disjoint.notMem_of_mem_left heP hfH
        exact (D.pathInterior_edgePath_disjoint hef).notMem_of_mem_left hinterP hinterG
  have mem_vertexP {z : X} (hzP : z ∈ (D.restrict hPG).support)
      (hzH : z ∈ (D.restrict hle).support) :
      z ∈ range (D.restrict hPG).vertex := by
    rw [support_eq, mem_union] at hzP
    rcases hzP with h | hE
    · exact h
    · obtain ⟨e, he⟩ := mem_iUnion.mp hE
      rw [range_edgePath_restrict] at he
      obtain hsrc | htgt | hinter :=
        (D.edgePath ⟨e.1, edgeSet_mono hPG e.2⟩).mem_range_iff_mem_interior_or_source_or_target z
          |>.mp he
      · refine ⟨edgeSource e, ?_⟩
        rw [restrict_vertex_edgeSource, hsrc]
      · refine ⟨edgeTarget e, ?_⟩
        rw [restrict_vertex_edgeTarget, htgt]
      · exact (not_intP hzH e (by rwa [hinterior hPG e])).elim
  have mem_vertexH {z : X} (hzP : z ∈ (D.restrict hPG).support)
      (hzH : z ∈ (D.restrict hle).support) :
      z ∈ range (D.restrict hle).vertex := by
    rw [support_eq, mem_union] at hzH
    rcases hzH with h | hE
    · exact h
    · obtain ⟨f, hf⟩ := mem_iUnion.mp hE
      rw [range_edgePath_restrict] at hf
      obtain hsrc | htgt | hinter :=
        (D.edgePath ⟨f.1, edgeSet_mono hle f.2⟩).mem_range_iff_mem_interior_or_source_or_target z
          |>.mp hf
      · refine ⟨edgeSource f, ?_⟩
        rw [restrict_vertex_edgeSource, hsrc]
      · refine ⟨edgeTarget f, ?_⟩
        rw [restrict_vertex_edgeTarget, htgt]
      · exact (not_intH hzP f (by rwa [hinterior hle f])).elim
  refine subset_antisymm ?_ ?_
  · intro z hz
    obtain h | h := hends (mem_vertexP hz.1 hz.2) (mem_vertexH hz.1 hz.2)
    · exact mem_insert_iff.mpr (Or.inl h)
    · exact mem_insert_iff.mpr (Or.inr (mem_singleton_iff.mpr h))
  · intro z hz
    simp only [mem_insert_iff, mem_singleton_iff] at hz
    have hfirstP : P.first ∈ V(P.toGraph) := by
      simp [WList.toGraph_vertexSet, WList.mem_vertexSet_iff]
    have hlastP : P.last ∈ V(P.toGraph) := by
      simp [WList.toGraph_vertexSet, WList.mem_vertexSet_iff]
    rcases hz with rfl | rfl
    · refine ⟨?_, ?_⟩
      · have := (D.restrict hPG).vertex_mem_support ⟨P.first, hfirstP⟩
        rwa [restrict_vertex] at this
      · have := (D.restrict hle).vertex_mem_support ⟨P.first, hP.first_mem⟩
        rwa [restrict_vertex] at this
    · refine ⟨?_, ?_⟩
      · have := (D.restrict hPG).vertex_mem_support ⟨P.last, hlastP⟩
        rwa [restrict_vertex] at this
      · have := (D.restrict hle).vertex_mem_support ⟨P.last, hP.last_mem⟩
        rwa [restrict_vertex] at this

end Ear

end Drawing

namespace PLDrawing

/-! ### Tracing a walk

A polygonal drawing assigns a polygonal path to each *edge*. Walking along a walk and concatenating
those paths gives a polygonal path whose image is the support of the drawing restricted to the
walk's graph. Both statements below are existence statements rather than definitions, for the same
reason `Drawing.IsPL` (`PLDrawing.lean:81`) is: the concatenation depends on an orientation choice
per edge — the walk traverses `e` from `edgeSource e` or from `edgeTarget e`, and `PolygonalPath`
is typed by its endpoints, so the two cases produce *different terms of different types*. The data
is not canonical under reversal or subdivision, so it is quantified away here as it is in
`PLDrawing.lean`.

No finiteness anywhere: a walk is finite by construction.
-/

/- **Route.** Induction on `W` with `WList.cons`. At `cons x e W'`, `PolygonalPath.append`
(`PolygonalPath/Basic.lean:342`) glues `D.cell ⟨e, _⟩` — reversed by `PolygonalPath.reverse`
(`:358`) when the walk traverses `e` against `edgeSource`/`edgeTarget` — onto the path for `W'`,
and `PolygonalPath.cast` retypes the shared endpoint.

*Simplicity* is `PolygonalPath.isSimple_append_iff` (`:701`); its two side conditions are exactly
what a graph path gives: `Drawing.range_edgePath_inter` (`Drawing.lean:171`) says two distinct
cells meet only in the images of shared ends, and `hW.nodup` says the walk revisits no vertex, so
consecutive cells meet only at the shared vertex image and non-consecutive ones not at all.

*The support equation* is `PolygonalPath.toSet_append` (`:556`) and `toSet_reverse` (`:564`)
against `Drawing.support_eq` (`Drawing.lean:137`), which expands a support as the union of the
cells and the vertex images; `PLDrawing.range_edgePath_restrictCell` (`PLDrawing.lean:107`)
identifies each restricted cell with the corresponding cell of `D`.

The obstruction that would otherwise send the prover back to first principles is the orientation
bookkeeping in the `cons` step. It is handled once, by `Drawing.restrict_vertex_edgeSource` /
`_edgeTarget` (`Drawing.lean:401,408`), which are what make `PLDrawing.restrictCell`
(`PLDrawing.lean:96`) typecheck without a reversal; the same two lemmas serve here. -/
/-- **A polygonal drawing of a path traces a simple polygonal arc**, from the image of the walk's
first vertex to the image of its last, whose image is exactly the support of the drawing restricted
to the walk. -/
theorem exists_polygonalPath_toSet_eq_support_of_isPath (D : PLDrawing G V) {W : WList α β}
    (hW : G.IsPath W) :
    ∃ A : PolygonalPath (D.toDrawing.vertex ⟨W.first, hW.isWalk.first_mem⟩)
        (D.toDrawing.vertex ⟨W.last, hW.isWalk.last_mem⟩),
      A.IsSimple ∧ A.toSet = (D.toDrawing.restrict hW.isWalk.toGraph_le).support := by
  revert hW
  induction W with
  | nil x =>
    intro hW
    have hxy : D.toDrawing.vertex ⟨(WList.nil x).first, hW.isWalk.first_mem⟩ =
        D.toDrawing.vertex ⟨(WList.nil x).last, hW.isWalk.last_mem⟩ :=
      congrArg D.toDrawing.vertex (Subtype.ext (by simp [WList.nil_first, WList.nil_last]))
    let A := (PolygonalPath.nil
        (D.toDrawing.vertex ⟨(WList.nil x).first, hW.isWalk.first_mem⟩)).cast rfl hxy
    refine ⟨A, (PolygonalPath.isSimple_cast rfl hxy).mpr (PolygonalPath.isSimple_nil _), ?_⟩
    rw [PolygonalPath.toSet_cast, PolygonalPath.toSet_nil]
    apply subset_antisymm
    · intro z hz
      simp only [mem_singleton_iff] at hz
      rw [hz]
      have hmem : (WList.nil x (β := β)).first ∈ V((WList.nil x (β := β)).toGraph) := by simp
      exact (Drawing.restrict_vertex D.toDrawing hW.isWalk.toGraph_le ⟨_, hmem⟩).symm ▸
        Drawing.vertex_mem_support _ ⟨_, hmem⟩
    · intro z hz
      rw [Drawing.support_eq, mem_union] at hz
      rcases hz with ⟨v, rfl⟩ | hE
      · have hv : v.1 = x := by
          simpa [WList.toGraph_vertexSet, WList.mem_vertexSet_iff] using v.2
        rw [Drawing.restrict_vertex]
        exact congrArg D.toDrawing.vertex
          (Subtype.ext (hv.trans (WList.nil_first (x := x) (β := β)).symm))
      · obtain ⟨ed, _⟩ := mem_iUnion.mp hE
        have : ed.1 ∈ E((WList.nil x (β := β)).toGraph) := ed.2
        simp at this
  | cons x e W' ih =>
    intro hW
    have hW' : G.IsPath W' := (cons_isPath_iff.mp hW).2.1
    have hxlink : G.IsLink e x W'.first := (cons_isPath_iff.mp hW).1
    have hxnot : x ∉ W' := (cons_isPath_iff.mp hW).2.2
    have hxe : e ∈ E(G) := hW.isWalk.edge_mem_of_mem (by simp)
    let eG : E(G) := ⟨e, hxe⟩
    have hne : x ≠ W'.first := fun h ↦ hxnot (h ▸ W'.first_mem)
    obtain ⟨A', hA's, hA'eq⟩ := ih hW'
    have hxy : D.toDrawing.vertex (edgeSource eG) ≠ D.toDrawing.vertex (edgeTarget eG) := by
      intro hvt
      have hse : edgeSource eG = edgeTarget eG := D.toDrawing.vertex_injective hvt
      rcases hxlink.eq_and_eq_or_eq_and_eq (isLink_edgeSource_edgeTarget eG) with
        ⟨hxs, hyt⟩ | ⟨hxt, hys⟩
      · exact hne (hxs.trans ((congrArg Subtype.val hse).trans hyt.symm))
      · exact hne (hxt.trans ((congrArg Subtype.val hse.symm).trans hys.symm))
    have hcell_simple : (D.cell eG).IsSimple :=
      (PolygonalPath.isSimpleArcOrLoop_iff_isSimple hxy).mp (D.cell_isSimpleArcOrLoop eG)
    have hB : ∃ B : PolygonalPath
        (D.toDrawing.vertex ⟨x, hW.isWalk.first_mem⟩)
        (D.toDrawing.vertex ⟨W'.first, hW'.isWalk.first_mem⟩),
        B.IsSimple ∧ B.toSet = range (D.toDrawing.edgePath eG) := by
      rcases hxlink.eq_and_eq_or_eq_and_eq (isLink_edgeSource_edgeTarget eG) with
        ⟨hxs, hyt⟩ | ⟨hxt, hys⟩
      · have hs : D.toDrawing.vertex (edgeSource eG) =
            D.toDrawing.vertex ⟨x, hW.isWalk.first_mem⟩ :=
          congrArg D.toDrawing.vertex (Subtype.ext hxs.symm)
        have ht : D.toDrawing.vertex (edgeTarget eG) =
            D.toDrawing.vertex ⟨W'.first, hW'.isWalk.first_mem⟩ :=
          congrArg D.toDrawing.vertex (Subtype.ext hyt.symm)
        refine ⟨(D.cell eG).cast hs ht, (PolygonalPath.isSimple_cast hs ht).mpr hcell_simple, ?_⟩
        rw [PolygonalPath.toSet_cast, D.range_edgePath]
      · have hs : D.toDrawing.vertex (edgeTarget eG) =
            D.toDrawing.vertex ⟨x, hW.isWalk.first_mem⟩ :=
          congrArg D.toDrawing.vertex (Subtype.ext hxt.symm)
        have ht : D.toDrawing.vertex (edgeSource eG) =
            D.toDrawing.vertex ⟨W'.first, hW'.isWalk.first_mem⟩ :=
          congrArg D.toDrawing.vertex (Subtype.ext hys.symm)
        refine ⟨(D.cell eG).reverse.cast hs ht,
          (PolygonalPath.isSimple_cast hs ht).mpr
            (PolygonalPath.isSimple_reverse.mpr hcell_simple), ?_⟩
        rw [PolygonalPath.toSet_cast, PolygonalPath.toSet_reverse, D.range_edgePath]
    obtain ⟨B, hBs, hBeq⟩ := hB
    have hlast : D.toDrawing.vertex ⟨W'.last, hW'.isWalk.last_mem⟩ =
        D.toDrawing.vertex ⟨(WList.cons x e W').last, hW.isWalk.last_mem⟩ :=
      congrArg D.toDrawing.vertex (Subtype.ext rfl)
    let A := B.append (A'.cast rfl hlast)
    have hend {z : V}
        (hz : z = D.toDrawing.vertex (edgeSource eG) ∨
          z = D.toDrawing.vertex (edgeTarget eG)) :
        z = D.toDrawing.vertex ⟨x, hW.isWalk.first_mem⟩ ∨
          z = D.toDrawing.vertex ⟨W'.first, hW'.isWalk.first_mem⟩ := by
      rcases hxlink.eq_and_eq_or_eq_and_eq (isLink_edgeSource_edgeTarget eG) with
        ⟨hxs, hyt⟩ | ⟨hxt, hys⟩
      · rcases hz with h | h
        · exact Or.inl (h.trans (congrArg D.toDrawing.vertex (Subtype.ext hxs.symm)))
        · exact Or.inr (h.trans (congrArg D.toDrawing.vertex (Subtype.ext hyt.symm)))
      · rcases hz with h | h
        · exact Or.inr (h.trans (congrArg D.toDrawing.vertex (Subtype.ext hys.symm)))
        · exact Or.inl (h.trans (congrArg D.toDrawing.vertex (Subtype.ext hxt.symm)))
    have hx_cell : D.toDrawing.vertex ⟨x, hW.isWalk.first_mem⟩ ∈
        range (D.toDrawing.edgePath eG) := by
      rcases hxlink.eq_and_eq_or_eq_and_eq (isLink_edgeSource_edgeTarget eG) with
        ⟨hxs, _⟩ | ⟨hxt, _⟩
      · exact ⟨0, (D.toDrawing.edgePath eG).source.trans
          (congrArg D.toDrawing.vertex (Subtype.ext hxs.symm))⟩
      · exact ⟨1, (D.toDrawing.edgePath eG).target.trans
          (congrArg D.toDrawing.vertex (Subtype.ext hxt.symm))⟩
    have hleWW : W'.toGraph ≤ (WList.cons x e W').toGraph := by
      rw [WList.toGraph_cons]
      exact Graph.left_le_union ..
    have hfirst : D.toDrawing.vertex ⟨x, hW.isWalk.first_mem⟩ =
        D.toDrawing.vertex ⟨(WList.cons x e W').first, hW.isWalk.first_mem⟩ := by
      simp [WList.first_cons]
    have hAs : A.IsSimple := by
      rw [PolygonalPath.isSimple_append_iff]
      refine ⟨hBs, (PolygonalPath.isSimple_cast rfl hlast).mpr hA's, ?_⟩
      intro z ⟨hzB', hzA'⟩
      have hzB : z ∈ range (D.toDrawing.edgePath eG) := hBeq ▸ hzB'
      have hzA : z ∈ (D.toDrawing.restrict hW'.isWalk.toGraph_le).support := by
        rwa [PolygonalPath.toSet_cast, hA'eq] at hzA'
      rw [Drawing.support_eq, mem_union] at hzA
      have hz_first : z = D.toDrawing.vertex ⟨W'.first, hW'.isWalk.first_mem⟩ := by
        rcases hzA with ⟨v, hv⟩ | hE
        · have hzV : z = D.toDrawing.vertex
              ⟨v.1, vertexSet_mono hW'.isWalk.toGraph_le v.2⟩ := by
            rw [← hv, Drawing.restrict_vertex]
          obtain hsrc | htgt | hinter :=
            (Path.mem_range_iff_mem_interior_or_source_or_target (X := V)
              (D.toDrawing.edgePath eG) z).mp hzB
          · rcases hend (Or.inl hsrc) with hx | hy
            · have hxv : x = v.1 := Subtype.ext_iff.mp <|
                D.toDrawing.vertex_injective (hx.symm.trans hzV)
              have hvW : v.1 ∈ W' := by
                simpa [WList.toGraph_vertexSet, WList.mem_vertexSet_iff] using v.2
              have : x ∈ W' := by rw [hxv]; exact hvW
              exact (hxnot this).elim
            · exact hy
          · rcases hend (Or.inr htgt) with hx | hy
            · have hxv : x = v.1 := Subtype.ext_iff.mp <|
                D.toDrawing.vertex_injective (hx.symm.trans hzV)
              have hvW : v.1 ∈ W' := by
                simpa [WList.toGraph_vertexSet, WList.mem_vertexSet_iff] using v.2
              have : x ∈ W' := by rw [hxv]; exact hvW
              exact (hxnot this).elim
            · exact hy
          · exact (D.toDrawing.pathInterior_edgePath_disjoint_vertex eG).notMem_of_mem_left
              hinter ⟨⟨v.1, vertexSet_mono hW'.isWalk.toGraph_le v.2⟩, hzV.symm⟩ |>.elim
        · obtain ⟨f, hf⟩ := mem_iUnion.mp hE
          rw [Drawing.range_edgePath_restrict] at hf
          have hef : eG ≠ ⟨f.1, edgeSet_mono hW'.isWalk.toGraph_le f.2⟩ := by
            intro h
            have heq : e = f.1 := Subtype.ext_iff.mp h
            have heW : e ∈ W'.edge := by
              simpa [WList.toGraph_edgeSet, WList.mem_edgeSet_iff, heq] using f.2
            have hnd := hW.edge_nodup
            rw [WList.cons_edge, List.nodup_cons] at hnd
            exact hnd.1 heW
          have hzinter :=
            (D.toDrawing.range_edgePath_inter hef).subset ⟨hzB, hf⟩
          have hzend : z = D.toDrawing.vertex (edgeSource eG) ∨
              z = D.toDrawing.vertex (edgeTarget eG) := by
            simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff] at hzinter
            exact hzinter.1
          rcases hend hzend with hx | hy
          · have hzf : z = D.toDrawing.vertex
                (edgeSource ⟨f.1, edgeSet_mono hW'.isWalk.toGraph_le f.2⟩) ∨
                z = D.toDrawing.vertex
                  (edgeTarget ⟨f.1, edgeSet_mono hW'.isWalk.toGraph_le f.2⟩) := by
              simp only [mem_inter_iff, mem_insert_iff, mem_singleton_iff] at hzinter
              exact hzinter.2
            have hxW : x ∈ V(W'.toGraph) := by
              rcases hzf with hfs | hft
              · have hxv := D.toDrawing.vertex_injective (hx.symm.trans hfs)
                have hxval : x = (edgeSource f).1 :=
                  (Subtype.ext_iff.mp hxv).trans (hW'.isWalk.toGraph_le.source f.2)
                rw [hxval]
                exact (edgeSource f).property
              · have hxv := D.toDrawing.vertex_injective (hx.symm.trans hft)
                have hxval : x = (edgeTarget f).1 :=
                  (Subtype.ext_iff.mp hxv).trans (hW'.isWalk.toGraph_le.target f.2)
                rw [hxval]
                exact (edgeTarget f).property
            have : x ∈ W' := by
              simpa [WList.toGraph_vertexSet, WList.mem_vertexSet_iff] using hxW
            exact (hxnot this).elim
          · exact hy
      simpa using hz_first
    have hAeq : A.toSet = (D.toDrawing.restrict hW.isWalk.toGraph_le).support := by
      rw [PolygonalPath.toSet_append, PolygonalPath.toSet_cast, hBeq, hA'eq]
      apply subset_antisymm
      · intro z hz
        rcases hz with hzB | hzW
        · have he_cons : e ∈ E((WList.cons x e W').toGraph) := by
            simp [WList.toGraph_edgeSet]
          have := Drawing.edgePath_range_subset_support
            (D.toDrawing.restrict hW.isWalk.toGraph_le) ⟨e, he_cons⟩
          rw [Drawing.range_edgePath_restrict] at this
          exact this hzB
        · rw [Drawing.support_eq, mem_union] at hzW ⊢
          rcases hzW with ⟨v, rfl⟩ | hE
          · refine Or.inl ⟨⟨v.1, vertexSet_mono hleWW v.2⟩, ?_⟩
            rw [Drawing.restrict_vertex, Drawing.restrict_vertex]
          · obtain ⟨f, hf⟩ := mem_iUnion.mp hE
            refine Or.inr (mem_iUnion.mpr ⟨⟨f.1, edgeSet_mono hleWW f.2⟩, ?_⟩)
            rw [Drawing.range_edgePath_restrict] at hf ⊢
            convert hf using 1
      · intro z hz
        rw [Drawing.support_eq, mem_union] at hz
        rcases hz with ⟨v, rfl⟩ | hE
        · have hvW : v.1 ∈ WList.cons x e W' := by
            simpa [WList.toGraph_vertexSet, WList.mem_vertexSet_iff] using v.2
          rw [WList.mem_cons_iff] at hvW
          rcases hvW with hxx | hvW'
          · have : (D.toDrawing.restrict hW.isWalk.toGraph_le).vertex v =
                D.toDrawing.vertex ⟨x, hW.isWalk.first_mem⟩ := by
              rw [Drawing.restrict_vertex]
              exact congrArg D.toDrawing.vertex (Subtype.ext hxx)
            rw [this]
            exact Or.inl hx_cell
          · refine Or.inr ?_
            have hmem : v.1 ∈ V(W'.toGraph) := by
              simpa [WList.toGraph_vertexSet, WList.mem_vertexSet_iff] using hvW'
            rw [Drawing.support_eq]
            refine Or.inl ⟨⟨v.1, hmem⟩, ?_⟩
            rw [Drawing.restrict_vertex, Drawing.restrict_vertex]
        · obtain ⟨f, hf⟩ := mem_iUnion.mp hE
          rw [Drawing.range_edgePath_restrict] at hf
          have hfE : f.1 ∈ (WList.cons x e W').edgeSet := by
            simpa [WList.toGraph_edgeSet] using f.2
          rw [WList.cons_edgeSet, mem_insert_iff] at hfE
          rcases hfE with hfE | hfW
          · have hfe : (⟨f.1, edgeSet_mono hW.isWalk.toGraph_le f.2⟩ : E(G)) = eG :=
              Subtype.ext hfE
            rw [hfe] at hf
            exact Or.inl hf
          · refine Or.inr ?_
            rw [Drawing.support_eq]
            refine Or.inr (mem_iUnion.mpr
              ⟨⟨f.1, by simpa [WList.toGraph_edgeSet] using hfW⟩, ?_⟩)
            rw [Drawing.range_edgePath_restrict]
            convert hf using 1
    refine ⟨A.cast hfirst rfl, (PolygonalPath.isSimple_cast hfirst rfl).mpr hAs, ?_⟩
    rw [PolygonalPath.toSet_cast]
    exact hAeq

/- **Route.** As above, but closing up: a cyclic walk is a closed trail with `W.tail.vertex.Nodup`,
so `PolygonalPath.isSimpleLoop_append_iff` (`SimpleLoop.lean:157`) applies to the split of `W` at
any interior vertex, its `hxy : x ≠ y` coming from `hW.nodup`. Loops of the graph are not a special
case to worry about *here* — a loop edge gives a one-edge cyclic walk whose cell is already an
embedded circle by `cell_isSimpleArcOrLoop` — but they are excluded by `[G.Loopless]` at every
consumer below. -/
/-- **A polygonal drawing of a cyclic walk traces a simple polygonal loop.** Digons and loop edges
are included: the cells of a drawing are disjoint but for their ends, so the traced loop is
embedded even when the walk has one or two edges. -/
theorem exists_isSimpleLoop_toSet_eq_support_of_isCyclicWalk (D : PLDrawing G V) {W : WList α β}
    (hW : G.IsCyclicWalk W) :
    ∃ A : PolygonalPath (D.toDrawing.vertex ⟨W.first, hW.isWalk.first_mem⟩)
        (D.toDrawing.vertex ⟨W.first, hW.isWalk.first_mem⟩),
      A.IsSimpleLoop ∧ A.toSet = (D.toDrawing.restrict hW.isWalk.toGraph_le).support := by
  sorry

/- **Route.** `isCycle_iff_exists_isCyclicWalk_eq` (`Forest.lean:207`) turns `hCcyc` into a cyclic
walk `W` with `W.toGraph = C`; `exists_isSimpleLoop_toSet_eq_support_of_isCyclicWalk` traces it;
`PolygonalPath.toPolygon` (`Polygon/PolygonalPath.lean:64`) is the polygon and
`boundary_toPolygon` (`:125`) the boundary equation — its `0 < P.length` side condition is
`IsSimpleLoop.length_pos` (`SimpleLoop.lean:82`). Simplicity transfers by
`Polygon.isSimple_iff_exists_isSimpleLoop` (`Polygon/PolygonalPath.lean:518`).

`Polygon.IsSimple` also carries `2 ≤ n` (`Polygon.IsSimple.two_le`, `Polygon/Basic.lean:349`), and
`n` here is `P.vertices.dropLast.length` — the number of *bends*, not of graph vertices. For a
digon `C` that is not automatic from `length_pos`; use `IsSimpleLoop.three_le_length`
(`SimpleLoop.lean:258`), which gives `3 ≤ P.length` for any simple loop and so covers the digon and
the loop edge at once. This is the step the module docstring argues informally ("at least one of
the two cells bends"); `three_le_length` is what discharges it, and it needs no case split.

The only real step is rewriting `(D.restrict hW.isWalk.toGraph_le).support` to
`(D.restrict hC).support` along `W.toGraph = C`; that is a `subst`, since `hC` and
`hW.isWalk.toGraph_le` are proofs of the same proposition once the graphs agree. -/
/-- The `Polygon` form of the previous lemma, used when a face is cut by a crosscut. -/
theorem exists_polygon_isSimple_of_isCycle (D : PLDrawing G V) (hC : C ≤ G) (hCcyc : C.IsCycle) :
    ∃ (n : ℕ) (p : Polygon V n),
      p.IsSimple ℝ ∧ p.boundary ℝ = (D.toDrawing.restrict hC).support := by
  sorry

/-! ### The face-cycle theorem -/

/- **Route for `exists_isCycle_frontier_faceSet_eq`.**

The seven steps are in this file's module docstring; this names the API for each.

*Setting up.* Faces are taken on `𝕊` throughout: `Drawing.onePoint` (`Face.lean:213`) transports
the drawing, `Drawing.isClosed_support_onePoint` (`Face.lean:228`) supplies the `IsClosed` argument
that `Drawing.faceSet_isOpen` (`Face.lean:177`) and `Drawing.frontier_faceSet_subset_support`
(`Face.lean:185`) need, and the plane bundle on `V` discharges its `[T2Space]` and
`[LocallyCompactSpace]` — the latter through `FiniteDimensional.of_fact_finrank_eq_two`, which is
a local instance in the `Plane` section below. `Drawing.support_onePoint` (`Face.lean:217`) moves support equations
across.

*Step 1.* `ConnGE.exists_isCycle_le` (`Forest.lean`) — note it returns `3 ≤ V(C₀).encard`, which
is precisely `ear_induction`'s `h3`, so do not reprove it.

*Step 2.* `ConnGE.ear_induction` (`Connected/Ear.lean`, and cited by name because that file is
being worked on). Signature at the time of writing:

    ConnGE.ear_induction [G.Finite] [G.Loopless] (hG : G.ConnGE 2) (hC₀ : C₀.IsCycle)
      (hC₀G : C₀ ≤ G) (h3 : 3 ≤ V(C₀).encard) {motive : Graph α β → Prop} (base : motive C₀)
      (step : ∀ ⦃H P⦄, C₀ ≤ H → H ≤ G → G.IsEar H P → motive H → motive (H ∪ P.toGraph)) :
      motive G

**Pass `motive` explicitly.** Its own docstring says why: `@[elab_as_elim]` infers the motive by
abstracting `G` out of the goal, and the motive wanted here is `fun H ↦ ∀ _ : H ≤ G, …`, in which
`G` occurs both as the abstracted variable and free in the binder's type. Abstraction cannot
produce that, and the resulting error is about elaboration, not about the mathematics.

*Step 3, base.* `exists_isSimpleLoop_toSet_eq_support_of_isCyclicWalk` above, then
`PolygonalPath.IsSimpleLoop.isJordanCurve` (`Geometry/Polygon/JordanCurve.lean:39`) and
`IsSimpleLoop.exists_sides_onePoint` (`:51`). Both sides are open, connected, disjoint from the
support and have frontier `|C₀|`, so `Drawing.exists_faceSet_eq` (`Face.lean:162`) makes each a
face; they cover the complement, so the given `F` is one of them.

`exists_sides_onePoint` is `sorry` — it is `Status.md` 3.2, and 3.2 is *not* covered by the §0
licence: §0 licenses `IsJordanCurve.exists_sides` alone and §3.1 derives the sphere form from it.
So this route depends on an open obligation that is somebody's work, not an assumption.

*Step 4.* The ear's relative interior misses `|H|` because its internal vertices are outside `V(H)`
(`IsEar.internal_disjoint`) and its edges outside `E(H)` (`IsEar.edge_disjoint`), and cells of a
drawing are pairwise disjoint off their ends — `Drawing.range_edgePath_inter` (`Drawing.lean:171`)
and `Drawing.pathInterior_edgePath_disjoint_vertex` (`Drawing.lean:157`). Connectedness of the
relative interior comes from the traced arc of
`exists_polygonalPath_toSet_eq_support_of_isPath` applied to `IsEar.isPath`. Landing it in one face
is `Drawing.faceSet_eq_connectedComponentIn` (`Face.lean:125`), which is hypothesis-free.

*Step 5.* `exists_two_regions_crosscut` (`ThetaCurve.lean:132`), fed by
`exists_polygon_isSimple_of_isCycle` above for its `p` and by
`exists_polygonalPath_toSet_eq_support_of_isPath` for its `A`. Its `hF` is stated with
`connectedComponentIn`, which is why this theorem's third conjunct is stated that way too — the
handoff is then a rewrite, not a construction. `Polygon.IsSimple.exists_arcs`
(`Polygon/PolygonalPath.lean:545`) supplies the two arcs of `|C|` if the caller needs them named.

That the two ends of `P` are images of *vertices of `C`* rather than merely points of `|C|` is the
one place the drawing axioms are used directly: `pathInterior_edgePath_disjoint_vertex` puts no
vertex image in an open cell, and `Drawing.vertex_injective` (`Drawing.lean:129`) then names the
vertex. `exists_two_regions_crosscut` is `sorry`, and so is `ConnGE.ear_induction`.

*Step 6.* `Drawing.restrict` is monotone in the subgraph, so `|H| ⊆ |H'|` follows from
`Drawing.support_eq` (`Drawing.lean:137`); `Drawing.exists_faceSet_eq` again recognises each
surviving face. `IsCyclicWalk.toGraph_isCycle` (`Forest.lean:192`) makes `C₁ + P` and `C₂ + P`
cycles, and `IsEar.union_le` (`Ear.lean:105`) puts them under `G`. -/
section Plane

attribute [local instance] FiniteDimensional.of_fact_finrank_eq_two

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (Module.finrank ℝ V = 2)]

/-- **The face theorem.** In a polygonal drawing of a finite loopless
`2`-connected graph, every face of the drawing on the sphere has a cycle of the graph as its
frontier, and *is* a connected component of the complement of that cycle.

The third conjunct is not implied by the second for a general set — it is what says the face is a
whole component of `𝕊 ∖ |C|` and not merely a set whose frontier happens to be `|C|`. It is stated
with `connectedComponentIn` rather than as "is a face of the restricted drawing" because that is
the form `exists_two_regions_crosscut` takes as a hypothesis, and §5 and §6 feed it straight in. -/
theorem exists_isCycle_frontier_faceSet_eq [G.Finite] [G.Loopless] (hG : G.ConnGE 2)
    (D : PLDrawing G V) (F : D.toDrawing.onePoint.Face) :
    ∃ (C : Graph α β) (hC : C ≤ G), C.IsCycle ∧
      frontier (D.toDrawing.onePoint.faceSet F) = (D.toDrawing.onePoint.restrict hC).support ∧
      ∀ ⦃q⦄, q ∈ D.toDrawing.onePoint.faceSet F →
        D.toDrawing.onePoint.faceSet F =
          connectedComponentIn ((D.toDrawing.onePoint.restrict hC).support)ᶜ q := by
  sorry

/- **Route.** `exists_isCycle_frontier_faceSet_eq`, then `⟨F, ‹_›⟩` for the existential in
`Drawing.IsFacialSubgraph` (`Face.lean:205`). One line once 4.2 lands; it exists so that
`Face.lean`'s consumers, stated against `IsFacialSubgraph`, do not each have to repackage. -/
/-- 4.2 in the packaged form `Face.lean`'s §5 and §6 statements are written against. Strictly
weaker than `exists_isCycle_frontier_faceSet_eq`, which names the face; use that one unless the
`IsFacialSubgraph` interface is what the caller already has. -/
theorem exists_isCycle_isFacialSubgraph [G.Finite] [G.Loopless] (hG : G.ConnGE 2)
    (D : PLDrawing G V) (F : D.toDrawing.onePoint.Face) :
    ∃ (C : Graph α β) (hC : C ≤ G), C.IsCycle ∧ D.toDrawing.onePoint.IsFacialSubgraph hC := by
  sorry

end Plane

end PLDrawing

end

end Graph
