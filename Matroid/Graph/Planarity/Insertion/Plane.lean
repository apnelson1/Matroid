module

public import Matroid.Graph.Planarity.Insertion.Basic
public import Matroid.Graph.Planarity.PLTopologicalMinor
public import Matroid.Graph.Planarity.StarLemma

@[expose] public section

/-!
# Edge insertion in the plane

This file supplies the two-dimensional geometric input for the ambient-space constructions in
`Insertion.Basic`: free polygonal arcs through faces and sectors, preservation of polygonality,
and the resulting planar edge, loop, and path insertion theorems.
-/

open Function Set Topology
open scoped unitInterval

universe u

variable {X : Type u} [TopologicalSpace X]

namespace Graph

public noncomputable section

variable {α β : Type*} {G : Graph α β} {u v : α} {f : β}

namespace Drawing

/-! ### The geometry

The combinators above are proved for arbitrary ambient spaces. The geometric inputs below are
polygonal: they choose a face incident with an edge or a sector at a vertex, then produce a free
polygonal arc. `IsFreePolygonalArc.isFreeArc` forgets the polygonal structure when calling
`Drawing.addEdge`; `isPL_addEdge` preserves it for later insertions.

The chain for a parallel edge is

`exists_face_frontier_superset_edgePath_interior` (a face incident with the open cell)
→ `vertex_mem_of_edgePath_interior_subset` (its ends lie on that frontier; proved)
→ `exists_freePolygonalArc_in_faceSet` (the routing primitive)
→ `IsFreePolygonalArc.isFreeArc` (proved)
→ `exists_isFreePolygonalArc_of_isLink` and `exists_isFreeArc_of_isLink` (proved)
→ `Planar.addEdge_of_isLink`.

For a loop the first three steps are replaced by `exists_isFreePolygonalArc_loop`, a triangle
inside one sector of the star at the vertex, and the rest is the same. `isPL_addEdge` is what makes
the result polygonal again, hence what lets Corollary 13.3 iterate 13.2; it is the reason the
geometry hands back a `PolygonalPath` and not just a `Path`. -/

section Geometry

open Metric
open scoped EuclideanSpace

/-- The polygonal form of `IsFreeArc`: an embedded polygonal arc — or an embedded circle, when its
two ends coincide, which is the loop case — meeting the drawing only at its ends.

This is what §13.1's geometry actually produces. `IsFreePolygonalArc.isFreeArc` forgets the
segments and hands `Drawing.addEdge` what it needs; `isPL_addEdge` keeps them. -/
structure IsFreePolygonalArc (D : Drawing G Plane) {z w : Plane}
    (Q : PolygonalPath z w) : Prop where
  isSimpleArcOrLoop : Q.IsSimpleArcOrLoop
  disjoint_support : Disjoint (Q.toSet \ {z, w}) D.support

/-- The bridge out of the polygonal category: `Path.interior_toPath` identifies the relative
interior of the parametrized arc with `toSet` minus the two ends, which is exactly the set
`IsFreePolygonalArc` controls. -/
lemma IsFreePolygonalArc.isFreeArc {D : Drawing G Plane} {z w : Plane} {Q : PolygonalPath z w}
    (hQ : D.IsFreePolygonalArc Q) : D.IsFreeArc Q.toPath where
  injOn := hQ.isSimpleArcOrLoop.injOn_toPath_Ioo
  disjoint_support := Path.interior_toPath_range hQ.isSimpleArcOrLoop hQ.disjoint_support

/-- An arc whose relative interior lies inside a face is free, because a face misses the support.
This is how the routing primitive's conclusion becomes an `IsFreePolygonalArc`. -/
lemma isFreePolygonalArc_of_subset_faceSet (D : Drawing G Plane) {z w : Plane}
    {Q : PolygonalPath z w} (F : D.Face) (hQ : Q.IsSimpleArcOrLoop)
    (hsub : Q.toSet \ {z, w} ⊆ D.faceSet F) : D.IsFreePolygonalArc Q where
  isSimpleArcOrLoop := hQ
  disjoint_support := (D.faceSet_disjoint_support F).mono_left hsub

/-- Plane form of `exists_sector_subset_connectedComponentIn`: a face whose frontier meets the
open star ball contains a whole sector of the punctured disk. -/
private lemma exists_sector_subset_faceSet_plane [G.Finite] (D : PLDrawing G Plane)
    {p q : Plane} {ρ : ℝ} {Y : Finset Plane} (hYne : Y.Nonempty)
    (hstar : closedBall p ρ ∩ D.toDrawing.support = {p} ∪ ⋃ y ∈ Y, segment ℝ p y)
    (hqball : q ∈ ball p ρ) {F : D.toDrawing.Face}
    (hqF : q ∈ frontier (D.toDrawing.faceSet F)) :
    ∃ C ∈ sectors p ρ Y, C ⊆ D.toDrawing.faceSet F := by
  obtain ⟨w, hw⟩ := D.toDrawing.faceSet_nonempty F
  rw [D.toDrawing.faceSet_eq_connectedComponentIn F hw] at hqF ⊢
  obtain ⟨z, hz⟩ :=
    mem_closure_iff.mp (frontier_subset_closure hqF) (ball p ρ) isOpen_ball hqball
  have hzball : z ∈ ball p ρ := hz.1
  have hzK : z ∈ connectedComponentIn D.toDrawing.supportᶜ w := hz.2
  have hzS : z ∉ D.toDrawing.support :=
    (connectedComponentIn_subset _ _ hzK)
  have hzD : z ∈ diskMinusRadii p ρ Y := by
    refine ⟨hzball, fun hzrad ↦ hzS ?_⟩
    have hzsup : z ∈ closedBall p ρ ∩ D.toDrawing.support := by
      rw [hstar]
      exact Or.inr (by simpa [mem_iUnion] using hzrad)
    exact hzsup.2
  refine ⟨connectedComponentIn (diskMinusRadii p ρ Y) z, ⟨z, hzD, rfl⟩, ?_⟩
  have hCsub := connectedComponentIn_subset (diskMinusRadii p ρ Y) z
  have hCS : connectedComponentIn (diskMinusRadii p ρ Y) z ⊆ D.toDrawing.supportᶜ := by
    intro w0 hw0 hwS
    have hw0D := hCsub hw0
    have hw0mem : w0 ∈ closedBall p ρ ∩ D.toDrawing.support :=
      ⟨ball_subset_closedBall hw0D.1, hwS⟩
    rw [hstar] at hw0mem
    obtain rfl | hwY := hw0mem
    · exact hw0D.2 (by
        obtain ⟨y, hy⟩ := hYne
        exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hy, left_mem_segment _ _ _⟩⟩)
    exact hw0D.2 (by simpa [mem_iUnion] using hwY)
  rw [connectedComponentIn_eq hzK]
  exact (isConnected_connectedComponentIn_iff.mpr hzD).isPreconnected.subset_connectedComponentIn
    (mem_connectedComponentIn hzD) hCS

/-- A sector of a two-radius star at an interior point of a cell lies off the drawing. -/
private lemma sector_subset_compl_support [G.Finite] (D : PLDrawing G Plane)
    {p : Plane} {ρ : ℝ} {Y : Finset Plane} {C : Set Plane} (hYne : Y.Nonempty)
    (hstar : closedBall p ρ ∩ D.toDrawing.support = {p} ∪ ⋃ y ∈ Y, segment ℝ p y)
    (hC : C ∈ sectors p ρ Y) : C ⊆ D.toDrawing.supportᶜ := by
  intro z hzC hzS
  have hzD := subset_diskMinusRadii_of_mem_sectors hC hzC
  have hzstar : z ∈ closedBall p ρ ∩ D.toDrawing.support :=
    ⟨ball_subset_closedBall hzD.1, hzS⟩
  rw [hstar] at hzstar
  obtain rfl | hzY := hzstar
  · exact hzD.2 (by
      obtain ⟨y, hy⟩ := hYne
      exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hy, left_mem_segment _ _ _⟩⟩)
  exact hzD.2 (by simpa [mem_iUnion] using hzY)

/-- The relative interior of an edge lies on the frontier of a face.

Take a sector of the two-radius star at any interior point; the face containing that sector has
the point on its frontier. Sector extraction and local constancy of the star along the open cell
spread this to the whole interior. This is the plane form of `facesAt_eq`, so it does not go
through `D.onePoint`. -/
theorem exists_face_frontier_superset_edgePath_interior [G.Finite] (D : PLDrawing G Plane)
    (e : E(G)) : ∃ F : D.Face, (D.edgePath e).Interior ⊆ frontier (D.faceSet F) := by
  have hPIne : ((D.edgePath e).Interior).Nonempty :=
    (isConnected_Ioo (show (0 : unitInterval) < 1 from zero_lt_one)).nonempty.image _
  obtain ⟨p, hp⟩ := hPIne
  obtain ⟨ρ, hρ, Y, hYsph, hYcard, _, hstar⟩ := D.exists_radius_edgeInterior hp
  have hYne : Y.Nonempty := Finset.card_pos.mp (by omega)
  have hsec : (sectors p ρ Y).ncard = 2 := by
    rw [ncard_sectors hρ hYne hYsph, hYcard]
  have hCne : (sectors p ρ Y).Nonempty := by
    have hfin : (sectors p ρ Y).Finite := finite_of_ncard_ne_zero (by rw [hsec]; norm_num)
    exact (ncard_pos (hs := hfin)).mp (by rw [hsec]; norm_num)
  obtain ⟨C, hC⟩ := hCne
  obtain ⟨x, hxC⟩ := (isConnected_of_mem_sectors hC).nonempty
  have hxS : x ∉ D.toDrawing.support := sector_subset_compl_support D hYne hstar hC hxC
  let F := D.toDrawing.faceAt hxS
  have hCface : C ⊆ D.toDrawing.faceSet F := by
    rw [D.toDrawing.faceSet_faceAt hxS]
    exact (isConnected_of_mem_sectors hC).isPreconnected.subset_connectedComponentIn hxC
      (sector_subset_compl_support D hYne hstar hC)
  have hp_sup : p ∈ D.toDrawing.support :=
    D.toDrawing.edgePath_range_subset_support e (Path.interior_subset_range _ hp)
  have hpF : p ∈ frontier (D.toDrawing.faceSet F) := by
    refine ⟨closure_mono hCface (mem_closure_of_mem_sectors hρ hYne hYsph hC), fun hint ↦ ?_⟩
    exact (D.toDrawing.faceSet_disjoint_support F).notMem_of_mem_left (interior_subset hint) hp_sup
  refine ⟨F, ?_⟩
  let PI := (D.edgePath e).Interior
  have hPIc : IsConnected PI := by
    simpa only [PI, Path.Interior] using
      (isConnected_Ioo (show (0 : unitInterval) < 1 from zero_lt_one)).image _
        (D.toDrawing.edgePath e).continuous.continuousOn
  let U : Set PI := {z | (z : Plane) ∈ frontier (D.toDrawing.faceSet F)}
  have hUeq : U = Subtype.val ⁻¹' closure (D.toDrawing.faceSet F) := by
    ext z
    change z.1 ∈ frontier (D.toDrawing.faceSet F) ↔ z.1 ∈ closure (D.toDrawing.faceSet F)
    rw [← closure_sdiff_interior, mem_sdiff]
    refine and_iff_left fun hint ↦ ?_
    exact (D.toDrawing.faceSet_disjoint_support F).notMem_of_mem_left (interior_subset hint)
      (D.toDrawing.edgePath_range_subset_support e (Path.interior_subset_range _ z.2))
  have hUclosed : IsClosed U := hUeq ▸ isClosed_closure.preimage continuous_subtype_val
  have hUne : U.Nonempty := ⟨⟨p, hp⟩, hpF⟩
  have hUopen : IsOpen U := by
    rw [isOpen_iff_forall_mem_open]
    intro z hzU
    obtain ⟨ρz, hρz, Yz, hYzsph, hYzcard, _, hstarz⟩ := D.exists_radius_edgeInterior z.2
    refine ⟨Subtype.val ⁻¹' ball (z : Plane) ρz,
      ?_, isOpen_ball.preimage continuous_subtype_val, mem_ball_self hρz⟩
    intro z' hz'
    have hzball : (z'.1 : Plane) ∈ ball z.1 ρz := hz'
    have hz'_sup : z'.1 ∈ D.toDrawing.support :=
      D.toDrawing.edgePath_range_subset_support e (Path.interior_subset_range _ z'.2)
    have hYzne : Yz.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨Cz, hCz, hCzface⟩ :=
      exists_sector_subset_faceSet_plane D hYzne hstarz (mem_ball_self hρz) hzU
    by_cases hz'z : z'.1 = z.1
    · simpa [U, hz'z] using hzU
    have hz'rad : z'.1 ∈ ⋃ y ∈ Yz, segment ℝ z.1 y := by
      have hz'star : z'.1 ∈ ({z.1} ∪ ⋃ y ∈ Yz, segment ℝ z.1 y : Set Plane) := by
        rw [← hstarz]
        exact ⟨ball_subset_closedBall hzball, hz'_sup⟩
      rw [mem_union, mem_singleton_iff] at hz'star
      exact hz'star.resolve_left hz'z
    obtain ⟨y, hyY, hyseg⟩ := mem_iUnion₂.mp hz'rad
    have hzy : z'.1 ≠ y := by
      intro h
      have hdist : Dist.dist z.1 z'.1 = ρz := by
        simpa [h, PseudoMetricSpace.dist_comm] using mem_sphere.mp (hYzsph hyY)
      have hdist' : Dist.dist z'.1 z.1 = ρz := by rwa [PseudoMetricSpace.dist_comm]
      exact (mem_ball.mp hzball).ne hdist'
    have hadj : {C ∈ sectors z.1 ρz Yz | z'.1 ∈ closure C} = sectors z.1 ρz Yz := by
      have hn := ncard_sectors_closure_eq_two hρz hYzsph (by omega) hyY
        ⟨hyseg, by simp [hz'z, hzy]⟩
      have hall : (sectors z.1 ρz Yz).ncard = 2 := by
        rw [ncard_sectors hρz hYzne hYzsph, hYzcard]
      have hsub : {C ∈ sectors z.1 ρz Yz | z'.1 ∈ closure C} ⊆ sectors z.1 ρz Yz :=
        sep_subset _ _
      have hfin : (sectors z.1 ρz Yz).Finite :=
        finite_of_ncard_ne_zero (by rw [hall]; norm_num)
      exact eq_of_subset_of_ncard_le hsub (by rw [hn, hall]) hfin
    have hz'_cl : z'.1 ∈ closure (D.toDrawing.faceSet F) := by
      have hCadj : z'.1 ∈ closure Cz := by
        have : Cz ∈ {C ∈ sectors z.1 ρz Yz | z'.1 ∈ closure C} := by
          rw [hadj]; exact hCz
        exact this.2
      exact closure_mono hCzface hCadj
    have hz'_not : z'.1 ∉ interior (D.toDrawing.faceSet F) := fun hint ↦
      (D.toDrawing.faceSet_disjoint_support F).notMem_of_mem_left (interior_subset hint) hz'_sup
    exact ⟨hz'_cl, hz'_not⟩
  have hUuniv : U = univ := by
    have : ConnectedSpace PI := isConnected_iff_connectedSpace.mp hPIc
    exact IsClopen.eq_univ ⟨hUclosed, hUopen⟩ hUne
  intro q hq
  have hqU : (⟨q, hq⟩ : PI) ∈ U := by
    rw [hUuniv]; trivial
  exact hqU

/-- The ends of an edge are limits of interior points of its arc, so any closed set containing the
relative interior contains both ends. With `S := frontier (D.faceSet F)` this is the sentence
"`p u, p v ∈ frontier W`, since they lie in `closure Γ̊_e`" of Lemma 13.2(1). Nothing polygonal, and
nothing two-dimensional. -/
lemma vertex_mem_of_edgePath_interior_subset (D : Drawing G X) (e : E(G)) {S : Set X}
    (hS : IsClosed S) (hsub : (D.edgePath e).Interior ⊆ S) :
    D.vertex (edgeSource e) ∈ S ∧ D.vertex (edgeTarget e) ∈ S := by
  have hmem : ∀ t : I, D.edgePath e t ∈ S := by
    intro t
    refine hS.closure_subset (closure_mono hsub (image_closure_subset_closure_image
      (D.edgePath e).continuous ⟨t, ?_, rfl⟩))
    rw [unitInterval.closure_Ioo_zero_one]
    trivial
  exact ⟨by simpa using hmem 0, by simpa using hmem 1⟩

/-- Two points on the frontier of a face are joined by a polygonal arc whose relative interior lies
inside the face.

*Open, and the genuinely two-dimensional input here.* This is the routing lemma used by the edge
insertion construction. -/
theorem exists_freePolygonalArc_in_faceSet [G.Finite] (D : PLDrawing G Plane)
    (F : D.toDrawing.Face) {z w : Plane} (hz : z ∈ frontier (D.toDrawing.faceSet F))
    (hw : w ∈ frontier (D.toDrawing.faceSet F)) :
    ∃ Q : PolygonalPath z w, Q.IsSimpleArcOrLoop ∧ Q.toSet \ {z, w} ⊆ D.toDrawing.faceSet F := by
  sorry

/-- **Lemma 13.2(1), parallel edge.** If `e` joins `u` and `v`, a polygonal drawing admits a free
polygonal arc between the images of `u` and `v`: route it through a face incident with `e`.

This is the assembly of the three lemmas above, and it is proved. -/
theorem exists_isFreePolygonalArc_of_isLink [G.Finite] (D : PLDrawing G Plane) {e : β}
    (he : G.IsLink e u v) :
    ∃ Q : PolygonalPath (D.vertex ⟨u, he.left_mem⟩) (D.vertex ⟨v, he.right_mem⟩),
      D.toDrawing.IsFreePolygonalArc Q := by
  obtain ⟨F, hF⟩ := exists_face_frontier_superset_edgePath_interior D ⟨e, he.edge_mem⟩
  obtain ⟨hs, ht⟩ := vertex_mem_of_edgePath_interior_subset D.toDrawing ⟨e, he.edge_mem⟩
    isClosed_frontier hF
  have hends := (isLink_edgeSource_edgeTarget (⟨e, he.edge_mem⟩ : E(G))).isLink_iff_sym2_eq.mp he
  have huv : D.vertex ⟨u, he.left_mem⟩ ∈ frontier (D.toDrawing.faceSet F) ∧
      D.vertex ⟨v, he.right_mem⟩ ∈ frontier (D.toDrawing.faceSet F) := by
    obtain ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ := Sym2.eq_iff.mp hends
    · have e₁ : (⟨u, he.left_mem⟩ : V(G)) = edgeSource (⟨e, he.edge_mem⟩ : E(G)) :=
        Subtype.ext h₁.symm
      have e₂ : (⟨v, he.right_mem⟩ : V(G)) = edgeTarget (⟨e, he.edge_mem⟩ : E(G)) :=
        Subtype.ext h₂.symm
      exact ⟨by rw [e₁]; exact hs, by rw [e₂]; exact ht⟩
    · have e₁ : (⟨u, he.left_mem⟩ : V(G)) = edgeTarget (⟨e, he.edge_mem⟩ : E(G)) :=
        Subtype.ext h₂.symm
      have e₂ : (⟨v, he.right_mem⟩ : V(G)) = edgeSource (⟨e, he.edge_mem⟩ : E(G)) :=
        Subtype.ext h₁.symm
      exact ⟨by rw [e₁]; exact ht, by rw [e₂]; exact hs⟩
  obtain ⟨Q, hQ, hsub⟩ := exists_freePolygonalArc_in_faceSet D F huv.1 huv.2
  exact ⟨Q, isFreePolygonalArc_of_subset_faceSet D.toDrawing F hQ hsub⟩

/-- **Lemma 13.2(2), loop.** A polygonal drawing of a finite graph admits a free polygonal loop at
every vertex.

*Open.* Route, verbatim from Status.md: take `ρ := ρ_{p v}` from the star lemma 3.6; by 3.5,
`ball (p v) ρ ∖ supp D` is a union of open sectors (the whole punctured ball if `deg v = 0`). Fix
one, with angular interval `(θᵢ, θᵢ₊₁)`, choose `θᵢ < θ' < θ'' < θᵢ₊₁` with `θ'' − θ' < π` and
`0 < r < ρ`, and take the boundary of the triangle with vertices `p v`, `p v + r·e^{iθ'}`,
`p v + r·e^{iθ''}`. Every point of that triangle has argument in `[θ', θ'']` and radius `≤ r`, so it
lies in the closed sector and meets `supp D` only at `p v`. That triangle is a `PolygonalPath` with
equal ends, so `IsSimpleArcOrLoop` is its circle case — which is why `IsFreeArc` was never allowed
to demand `u ≠ v`. -/
theorem exists_isFreePolygonalArc_loop [G.Finite] (D : PLDrawing G Plane) (hu : u ∈ V(G)) :
    ∃ Q : PolygonalPath (D.vertex ⟨u, hu⟩) (D.vertex ⟨u, hu⟩),
      D.toDrawing.IsFreePolygonalArc Q := by
  sorry

/-- Lemma 13.2(1) in the form `Drawing.addEdge` consumes. -/
theorem exists_isFreeArc_of_isLink [G.Finite] (D : PLDrawing G Plane) {e : β}
    (he : G.IsLink e u v) :
    ∃ γ : Path (D.vertex ⟨u, he.left_mem⟩) (D.vertex ⟨v, he.right_mem⟩),
      D.toDrawing.IsFreeArc γ := by
  obtain ⟨Q, hQ⟩ := exists_isFreePolygonalArc_of_isLink D he
  exact ⟨Q.toPath, hQ.isFreeArc⟩

/-- Lemma 13.2(2) in the form `Drawing.addEdge` consumes. -/
theorem exists_isFreeArc_loop [G.Finite] (D : PLDrawing G Plane) (hu : u ∈ V(G)) :
    ∃ γ : Path (D.vertex ⟨u, hu⟩) (D.vertex ⟨u, hu⟩), D.toDrawing.IsFreeArc γ := by
  obtain ⟨Q, hQ⟩ := exists_isFreePolygonalArc_loop D hu
  exact ⟨Q.toPath, hQ.isFreeArc⟩

/-- Inserting an edge along a *polygonal* free arc keeps the drawing polygonal. This is what lets
Corollary 13.3 apply Lemma 13.2 again to the drawing it just produced, and it is the reason the two
existence lemmas above hand back a `PolygonalPath`.

*Open.* Route: `PLDrawing.ofCells` with `addEdgeVertex` for the vertices, the old cells transported
by `PolygonalPath.cast` exactly as in `PLDrawing.restrictCell`, and `Q` — reversed if `ArbRel`
disagrees, the polygonal analogue of `Path.reorient` — as the cell of `f`. Its four obligations are
the `toSet`-level forms of `addEdgeEdge_injOn`, `addEdgeEdge_interior_disjoint_vertex` and
`addEdgeEdge_interior_disjoint`, already discharged above at the `Path.Interior` level; the
translation between the two levels is `Path.interior_toPath`. -/
theorem isPL_addEdge [G.Finite] (D : PLDrawing G Plane) (hu : u ∈ V(G)) (hv : v ∈ V(G))
    (hf : f ∉ E(G)) {Q : PolygonalPath (D.vertex ⟨u, hu⟩) (D.vertex ⟨v, hv⟩)}
    (hQ : D.toDrawing.IsFreePolygonalArc Q) :
    (D.toDrawing.addEdge hu hv hf Q.toPath hQ.isFreeArc).IsPL := by
  sorry

end Geometry

end Drawing

/-! ### Planarity

These corollaries choose a drawing, obtain a free arc, and apply the insertion combinator. The
edge and loop results start from `PLPlanar` because their geometric inputs are polygonal; path
insertion accepts an ordinary plane drawing.
-/

namespace PLPlanar

variable {e : β}

/-- Adding an edge parallel to an existing one keeps a finite graph planar. -/
theorem addEdge_of_isLink [G.Finite] (hG : G.PLPlanar) (he : G.IsLink e u v) (hf : f ∉ E(G)) :
    (G.addEdge f u v).Planar := by
  obtain ⟨D⟩ := hG
  obtain ⟨γ, hγ⟩ := Drawing.exists_isFreeArc_of_isLink D he
  exact ⟨D.toDrawing.addEdge he.left_mem he.right_mem hf γ hγ⟩

/-- Adding a loop keeps a finite graph planar. -/
theorem addLoop [G.Finite] (hG : G.PLPlanar) (hu : u ∈ V(G)) (hf : f ∉ E(G)) :
    (G.addEdge f u u).Planar := by
  obtain ⟨D⟩ := hG
  obtain ⟨γ, hγ⟩ := Drawing.exists_isFreeArc_loop D hu
  exact ⟨D.toDrawing.addEdge hu hu hf γ hγ⟩

end PLPlanar

namespace Planar

variable {e : β}

/-- Inserting a subdivided edge along a free arc of a plane drawing. -/
theorem addPath_of_isFreeArc {P : WList α β} (D : Drawing G Plane) (hP : P.toGraph.IsPath P)
    (hu : u ∈ V(G)) (hv : v ∈ V(G)) (hends : P.first = u ∧ P.last = v)
    (hint : V(G) ∩ V(P.toGraph) = {P.first, P.last}) (hE : Disjoint E(G) E(P.toGraph))
    (γ : Path (D.vertex ⟨u, hu⟩) (D.vertex ⟨v, hv⟩)) (hγ : D.IsFreeArc γ) :
    (G ∪ P.toGraph).Planar :=
  ⟨D.addPath hP hu hv hends hint hE γ hγ⟩

end Planar

end

end Graph
