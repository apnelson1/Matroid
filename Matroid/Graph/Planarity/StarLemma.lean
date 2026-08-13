import Matroid.Graph.Planarity.PLDrawing
import Matroid.Graph.Planarity.Face
import Matroid.ForMathlib.Geometry.DiskMinusRadii
import Matroid.ForMathlib.Geometry.SegmentFigure
import Matroid.ForMathlib.Geometry.StarComponents
import Matroid.ForMathlib.Topology.ConnPartition
import Matroid.ForMathlib.Analysis.Convex.RadialPoint
import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# The local structure of a polygonal drawing

Status.md 3.6–3.8. Near any of its points, a polygonal drawing of a finite graph is a star of
finitely many straight radii, and that is all the local structure the rest of the development needs.
This is the payoff of working in the polygonal category: for an arbitrary drawing these statements
are Schoenflies-strength, and here they are elementary.

## What each statement costs

`exists_radius` — the star lemma itself — is stated over a **real normed space**, not the plane: a
finite union of segments looks like a star near each of its points whatever the ambient dimension.
Only the accessibility and locally-constant-sides statements need the plane, because only they count
the pieces the radii cut the neighbourhood into, and that count is `d` only in dimension two
(`Matroid.ForMathlib.Geometry.DiskMinusRadii`).

Loops are allowed throughout. Status.md assumes looplessness in 3.6; that is inherited from §2 and
is not needed here — a loop at `v` simply contributes two of the radii at `v`, which is what
`degree` already counts.

Faces are taken on the sphere, since that is where §§4–6 use them.

## Main statements

* `PLDrawing.exists_radius` : the star lemma, over any real normed space.
* `PLDrawing.exists_radius_vertex`, `PLDrawing.exists_radius_edgeInterior` : the two cases, with the
  number of radii identified.
* `PLDrawing.exists_segment_sdiff_subset_faceSet` : Status.md 3.7, accessibility.
* `PLDrawing.ncard_faces_at_edgeInterior_le_two` and `PLDrawing.faces_at_edgeInterior_eq` :
  Status.md 3.8, the two sides of an open cell and their local constancy.
-/

open Function Set Topology Metric

namespace Graph

noncomputable section

universe u

variable {α β : Type*} {G H : Graph α β}
variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

namespace PLDrawing

/-! ### 3.6, the star lemma -/

/- `exists_radius` used to be proved here, over ~125 lines. Its proof used the drawing exactly
twice, both as `range D.toDrawing.vertex` and both times only for finiteness; everything else came
from `exists_finite_support`, whose conclusion is `IsSegmentFigure`. It is therefore a fact about
finite unions of segments, and now lives in `Matroid/ForMathlib/Geometry/SegmentFigure.lean`
(Kuratowski `Decisions.md` D14: a file mentioning no `Graph`, `V(`, `E(` is not a planarity file).

Moving it is what unblocks Status.md 3.9: a θ-curve is three polygonal arcs with no drawing
anywhere, so it could never reach the drawing-shaped statement, and manufacturing a `PLDrawing` of
`Graph.banana` to fake one leads back to `exists_radius_vertex`, whose degree conjunct is still
open (SegmentFigure counting is done; see the handoff on that theorem). -/

/- Dropped `Y.Nonempty`: Status.md's `d ≥ 1` conflicts with `d = deg v` at isolated vertices;
the star there is `{p}` with `Y = ∅`, so the equality uses `{p} ∪ ⋃ …`. -/

/-- The support of a polygonal drawing of a finite graph is a segment figure. This is the whole of
what the star lemma uses about a drawing. -/
theorem isSegmentFigure_support [G.Finite] (D : PLDrawing G V) :
    IsSegmentFigure D.toDrawing.support := by
  obtain ⟨S, hSfin, hsupp⟩ := D.exists_finite_support
  exact ⟨_, S, Set.finite_range _, hSfin, hsupp⟩

/-- **The star lemma.** About each of its points, a polygonal drawing of a finite graph meets a
small enough closed ball in a union of straight radii, one for each direction in which the drawing
leaves the point.

No hypothesis on the ambient space beyond a norm. This is `IsSegmentFigure.exists_radius`
specialised along `isSegmentFigure_support`; nothing about graphs enters its proof. -/
theorem exists_radius [G.Finite] (D : PLDrawing G V) {p : V} (hp : p ∈ D.toDrawing.support) :
    ∃ ρ > 0, ∃ Y : Finset V, ↑Y ⊆ sphere p ρ ∧
      closedBall p ρ ∩ D.toDrawing.support = {p} ∪ ⋃ y ∈ Y, segment ℝ p y :=
  D.isSegmentFigure_support.exists_radius hp

/-- At a point interior to one cell there are exactly two radii, and both lie along that cell. -/
theorem exists_radius_edgeInterior [G.Finite] (D : PLDrawing G V) {e : E(G)} {p : V}
    (hp : p ∈ pathInterior (D.toDrawing.edgePath e)) :
    ∃ ρ > 0, ∃ Y : Finset V, ↑Y ⊆ sphere p ρ ∧ Y.card = 2 ∧ ↑Y ⊆ range (D.toDrawing.edgePath e) ∧
    closedBall p ρ ∩ D.toDrawing.support = {p} ∪ ⋃ y ∈ Y, segment ℝ p y := by
  classical
  have hp_cell : p ∈ (D.cell e).toSet := D.range_edgePath e ▸ (pathInterior_subset_range _ hp)
  by_cases hvert : p ∈ (D.cell e).vertices
  · -- Bend at an interior polygonal vertex: two incident cell edges, then the open-segment star.
    have hp_not_v : p ∉ range D.toDrawing.vertex :=
      (Drawing.pathInterior_edgePath_disjoint_vertex D.toDrawing e).notMem_of_mem_left hp
    have hpx : p ≠ D.toDrawing.vertex (edgeSource e) := fun h ↦ hp_not_v ⟨_, h.symm⟩
    have hpy : p ≠ D.toDrawing.vertex (edgeTarget e) := fun h ↦ hp_not_v ⟨_, h.symm⟩
    obtain ⟨A, B, hAB⟩ := (D.cell e).exists_append_eq_of_mem_vertices hvert
    have hApos : 0 < A.length := by
      by_contra hA
      have : A.length = 0 := Nat.eq_zero_of_not_pos hA
      cases A with
      | nil => exact hpx rfl
      | cons => simp at this
    have hBpos : 0 < B.length := by
      by_contra hB
      have : B.length = 0 := Nat.eq_zero_of_not_pos hB
      cases B with
      | nil => exact hpy rfl
      | cons => simp at this
    obtain ⟨a, haA⟩ := A.exists_edge_ending_at_last hApos
    obtain ⟨b, hbB⟩ := B.exists_edge_starting_at_first hBpos
    have ha : (a, p) ∈ (D.cell e).edges := by
      simpa [hAB, PolygonalPath.append_edges] using Or.inl haA
    have hb : (p, b) ∈ (D.cell e).edges := by
      simpa [hAB, PolygonalPath.append_edges] using Or.inr hbB
    have hA : A.IsSimple := (hAB ▸ D.cell_isSimpleArcOrLoop e).isSimple_left hpx.symm
    have hB : B.IsSimple := (hAB ▸ D.cell_isSimpleArcOrLoop e).isSimple_right hpx.symm
    have hne_a : a ≠ p := hA.hasNondegenerateEdges _ haA
    have hne_b : b ≠ p := (hB.hasNondegenerateEdges _ hbB).symm
    have honly : ∀ s ∈ (D.cell e).edges, p ∈ segment ℝ s.1 s.2 → s = (a, p) ∨ s = (p, b) := by
      intro s hs hps
      have hs' : s ∈ A.edges ∨ s ∈ B.edges := by
        simpa [hAB, PolygonalPath.append_edges] using hs
      rcases hs' with hsA | hsB
      · exact Or.inl (PolygonalPath.eq_last_edge_of_mem_segment hA haA hsA hps)
      · exact Or.inr (PolygonalPath.eq_first_edge_of_mem_segment hB hbB hsB hps)
    have hinter : A.toSet ∩ B.toSet ⊆ ({D.toDrawing.vertex (edgeSource e), p} : Set V) := by
      intro u hu
      obtain ⟨hS, _⟩ | ⟨heq', hL⟩ := hAB ▸ D.cell_isSimpleArcOrLoop e
      · exact Or.inr ((PolygonalPath.isSimple_append_iff.mp hS).2.2 hu)
      · let B' : PolygonalPath p (D.toDrawing.vertex (edgeSource e)) := B.cast rfl heq'
        have hBset : B'.toSet = B.toSet := PolygonalPath.toSet_cast B rfl heq'
        have hL' : (A.append B').IsSimpleLoop := by
          dsimp [B']
          rwa [← PolygonalPath.append_cast_right A B heq']
        exact ((PolygonalPath.isSimpleLoop_append_iff hpx.symm).mp hL').2.2 ▸ ⟨hu.1, hBset ▸ hu.2⟩
    have ha_not_other {f : E(G)} (hf : f ≠ e) : p ∉ (D.cell f).toSet := by
      intro hpf
      obtain ⟨t, rfl⟩ := D.range_edgePath f ▸ hpf
      obtain rfl | h0 := eq_or_ne t 0
      · exact hp_not_v (by rw [(D.edgePath f).source]; exact ⟨_, rfl⟩)
      obtain rfl | h1 := eq_or_ne t 1
      · exact hp_not_v (by rw [(D.edgePath f).target]; exact ⟨_, rfl⟩)
      · exact (Drawing.pathInterior_edgePath_disjoint D.toDrawing hf.symm).notMem_of_mem_left hp
          ⟨t, ⟨lt_of_le_of_ne t.2.1 h0.symm, lt_of_le_of_ne t.2.2 h1⟩, rfl⟩
    have hcellCompact (f : E(G)) : IsCompact (D.cell f).toSet := by
      rw [PolygonalPath.toSet_eq_insert_biUnion]
      exact isCompact_singleton.union <|
        ((D.cell f).edges.finite_toSet).isCompact_biUnion fun _ _ ↦ isCompact_segment _ _
    let T : Set (V × V) := {s | s ∈ (D.cell e).edges ∧ p ∉ segment ℝ s.1 s.2}
    let Kcell : Set V := ⋃ s ∈ T, segment ℝ s.1 s.2
    let Kfor : Set V := range D.toDrawing.vertex ∪ ⋃ f ∈ {f : E(G) | f ≠ e}, (D.cell f).toSet
    let K : Set V := Kfor ∪ Kcell
    have hKclosed : IsClosed K := by
      refine IsClosed.union (IsClosed.union ?_ ?_) ?_
      · have : Finite V(G) := inferInstance
        exact (Set.finite_range D.toDrawing.vertex).isCompact.isClosed
      · exact ((Set.toFinite _).isCompact_biUnion fun f _ ↦ hcellCompact f).isClosed
      · exact ((D.cell e).edges.finite_toSet.subset fun _ h ↦ h.1).isCompact_biUnion
          (fun _ _ ↦ isCompact_segment _ _) |>.isClosed
    have hpK : p ∉ K := by
      refine not_or.mpr ⟨not_or.mpr ⟨hp_not_v, fun hp' ↦ ?_⟩, fun hp' ↦ ?_⟩ <;>
        obtain ⟨f, hf, hpf⟩ := mem_iUnion₂.mp hp'
      · exact ha_not_other hf hpf
      · exact hf.2 hpf
    obtain ⟨δ, hδpos, hδle⟩ := exists_pos_le_dist_of_notMem hKclosed hpK
    let ρ : ℝ := min δ (min (dist p a) (dist p b)) / 2
    have hρpos : 0 < ρ :=
      half_pos (lt_min hδpos (lt_min (dist_pos.mpr hne_a.symm) (dist_pos.mpr hne_b.symm)))
    have hρ_lt_δ : ρ < δ :=
      calc
        ρ ≤ δ / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
        _ < δ := half_lt_self hδpos
    have hρ_le_a : ρ ≤ dist p a :=
      calc
        ρ ≤ min (dist p a) (dist p b) / 2 :=
          div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
        _ ≤ dist p a / 2 :=
          div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
        _ ≤ dist p a := half_le_self dist_nonneg
    have hρ_le_b : ρ ≤ dist p b :=
      calc
        ρ ≤ min (dist p a) (dist p b) / 2 :=
          div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
        _ ≤ dist p b / 2 :=
          div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
        _ ≤ dist p b := half_le_self dist_nonneg
    have hnotK {x : V} (hxball : x ∈ closedBall p ρ) (hxK : x ∈ K) : False := by
      have hle := hδle x hxK
      rw [PseudoMetricSpace.dist_comm] at hle
      linarith [mem_closedBall.mp hxball, hρ_lt_δ]
    let ya := radialPoint p a ρ
    let yb := radialPoint p b ρ
    let Y : Finset V := {ya, yb}
    have hsegA : segment ℝ a p ⊆ A.toSet := A.segment_subset_toSet haA
    have hsegB : segment ℝ p b ⊆ B.toSet := B.segment_subset_toSet hbB
    have hsegA' : segment ℝ p a ⊆ A.toSet := by rw [segment_symm]; exact hsegA
    have hneY : ya ≠ yb := by
      -- Either way round, the two radii being equal puts one of `a`, `b` on the segment from `p`
      -- to the other, so the whole segment from `p` to that point lies in both `A` and `B`. Its
      -- midpoint then contradicts `hinter`, which allows only `p` and the source vertex there.
      have key {c : V} (hne_c : c ≠ p) (hA : segment ℝ p c ⊆ A.toSet)
          (hB : segment ℝ p c ⊆ B.toSet) : False := by
        obtain hc_src | hc_p :=
          mem_insert_iff.mp (hinter ⟨hA (right_mem_segment ℝ p c), hB (right_mem_segment ℝ p c)⟩)
        · have hz_open : AffineMap.lineMap p c (1 / 2 : ℝ) ∈ openSegment ℝ p c := by
            rw [openSegment_eq_image_lineMap]
            exact ⟨1 / 2, ⟨by norm_num, by norm_num⟩, rfl⟩
          have hz_seg := openSegment_subset_segment ℝ p c hz_open
          obtain h1 | h2 := mem_insert_iff.mp (hinter ⟨hA hz_seg, hB hz_seg⟩)
          · exact (ne_of_mem_openSegment_right hne_c.symm hz_open).symm (h1.trans hc_src.symm)
          exact (ne_of_mem_openSegment_left hne_c.symm hz_open).symm (mem_singleton_iff.mp h2)
        exact hne_c (mem_singleton_iff.mp hc_p)
      intro heq
      obtain ⟨t, ht, hab⟩ := (radialPoint_eq_iff_pos_parallel p a b hρpos hne_a hne_b).mp heq
      obtain ht1 | ht1 := le_or_gt t 1
      · have ha_seg : a ∈ segment ℝ p b := by
          have ha_eq : a = AffineMap.lineMap p b t := by
            simp only [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub]
            rw [← hab]; abel
          rw [ha_eq, segment_eq_image_lineMap]
          exact ⟨t, ⟨ht.le, ht1⟩, rfl⟩
        exact key hne_a hsegA'
          (((convex_segment p b).segment_subset (left_mem_segment _ _ _) ha_seg).trans hsegB)
      have hb_seg : b ∈ segment ℝ p a := by
        have hab' : b - p = t⁻¹ • (a - p) := by
          have h := congrArg (fun z : V ↦ t⁻¹ • z) hab.symm
          simpa [smul_smul, inv_mul_cancel₀ ht.ne', one_smul] using h
        have hb_eq : b = AffineMap.lineMap p a t⁻¹ := by
          simp only [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub]
          rw [← hab', sub_add_cancel]
        rw [hb_eq, segment_eq_image_lineMap]
        exact ⟨t⁻¹, ⟨inv_nonneg.mpr ht.le, inv_le_one_iff₀.mpr (Or.inr ht1.le)⟩, rfl⟩
      exact key hne_b
        (((convex_segment p a).segment_subset (left_mem_segment _ _ _) hb_seg).trans hsegA') hsegB
    have hYcard : Y.card = 2 := Finset.card_pair hneY
    have hYsph : ↑Y ⊆ sphere p ρ := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact mem_sphere_radialPoint p a hρpos.le hne_a
      · rw [Finset.mem_singleton.mp hy]; exact mem_sphere_radialPoint p b hρpos.le hne_b
    have hYrange : ↑Y ⊆ range (D.toDrawing.edgePath e) := by
      intro y hy
      have hcell : segment ℝ a p ∪ segment ℝ p b ⊆ (D.cell e).toSet := by
        rw [hAB, PolygonalPath.toSet_append]
        exact union_subset_union hsegA hsegB
      have hcell' : segment ℝ a p ∪ segment ℝ p b ⊆ range (D.toDrawing.edgePath e) := by
        simpa [D.range_edgePath e] using hcell
      rcases Finset.mem_insert.mp hy with rfl | hy
      · have hrad := radialPoint_mem_segment p a hρpos.le hρ_le_a
        have : ya ∈ segment ℝ a p := by rwa [segment_symm] at hrad
        exact hcell' (Or.inl this)
      · rw [Finset.mem_singleton.mp hy]
        have hrad := radialPoint_mem_segment p b hρpos.le hρ_le_b
        exact hcell' (Or.inr hrad)
    refine ⟨ρ, hρpos, Y, hYsph, hYcard, hYrange, ?_⟩
    have hloc : closedBall p ρ ∩ D.toDrawing.support =
        closedBall p ρ ∩ (segment ℝ a p ∪ segment ℝ p b) := by
      ext x
      refine ⟨fun ⟨hxball, hxsup⟩ ↦ ⟨hxball, ?_⟩, fun ⟨hxball, hxseg⟩ ↦ ⟨hxball, ?_⟩⟩
      · refine (D.support_eq ▸ hxsup).elim (fun hxV ↦ (hnotK hxball (Or.inl (Or.inl hxV))).elim) fun hxE ↦ ?_
        obtain ⟨f, hf⟩ := mem_iUnion.mp hxE
        rw [D.range_edgePath f] at hf
        by_cases hef : f = e
        · rw [hef] at hf
          have hPpos : 0 < (D.cell e).length := by
            rw [← (D.cell e).edges_length]
            exact List.length_pos_of_mem ha
          obtain ⟨s, hs, hxs⟩ := (PolygonalPath.mem_toSet_iff (D.cell e) hPpos).mp hf
          by_cases hps : p ∈ segment ℝ s.1 s.2
          · rcases honly s hs hps with rfl | rfl
            · exact Or.inl hxs
            · exact Or.inr hxs
          · exact (hnotK hxball (Or.inr (mem_iUnion₂.mpr ⟨s, ⟨hs, hps⟩, hxs⟩))).elim
        · exact (hnotK hxball (Or.inl (Or.inr (mem_iUnion₂.mpr ⟨f, hef, hf⟩)))).elim
      · have : x ∈ (D.cell e).toSet := by
          rw [hAB, PolygonalPath.toSet_append]
          exact hxseg.elim (fun h ↦ Or.inl (hsegA h)) (fun h ↦ Or.inr (hsegB h))
        rw [← D.range_edgePath e] at this
        exact Drawing.edgePath_range_subset_support _ _ this
    have hYunion : (⋃ y ∈ Y, segment ℝ p y) = segment ℝ p ya ∪ segment ℝ p yb := by
      simp [Y]
    rw [hloc, closedBall_inter_two_segments_at_endpoint p a b hρpos hne_a hne_b hρ_le_a hρ_le_b,
      two_radii_union_eq_star p ya yb, ← hYunion]
  · obtain ⟨s, ⟨hs, has⟩, _⟩ :=
      (D.cell_isSimpleArcOrLoop e).existsUnique_edge hp_cell hvert
    have hne1 : s.1 ≠ p := fun h ↦ hvert (h ▸ (D.cell e).fst_mem_vertices hs)
    have hne2 : s.2 ≠ p := fun h ↦ hvert (h ▸ (D.cell e).snd_mem_vertices hs)
    have hab : s.1 ≠ s.2 := fun heq ↦ by
      have : p = s.1 := by simpa [heq, segment_same] using has
      exact hne1 this.symm
    have hp_open : p ∈ openSegment ℝ s.1 s.2 := mem_openSegment_of_ne_left_right hne1 hne2 has
    obtain ⟨U, hU, hUeq⟩ :=
      D.exists_nhds_inter_support_eq_segment (f := e) hp_cell hvert hs has
    obtain ⟨ε, hεpos, hεU⟩ := Metric.mem_nhds_iff.mp hU
    let ρ : ℝ := min ε (min (dist p s.1) (dist p s.2)) / 2
    have hρpos : 0 < ρ :=
      half_pos (lt_min hεpos (lt_min (dist_pos.mpr hne1.symm) (dist_pos.mpr hne2.symm)))
    have hρ_lt_ε : ρ < ε :=
      calc
        ρ ≤ ε / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
        _ < ε := half_lt_self hεpos
    have hρ_le_a : ρ ≤ dist p s.1 :=
      calc
        ρ ≤ min (dist p s.1) (dist p s.2) / 2 :=
          div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
        _ ≤ dist p s.1 / 2 :=
          div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
        _ ≤ dist p s.1 := half_le_self dist_nonneg
    have hρ_le_b : ρ ≤ dist p s.2 :=
      calc
        ρ ≤ min (dist p s.1) (dist p s.2) / 2 :=
          div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
        _ ≤ dist p s.2 / 2 :=
          div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
        _ ≤ dist p s.2 := half_le_self dist_nonneg
    have hball_U : closedBall p ρ ⊆ U :=
      (closedBall_subset_ball hρ_lt_ε).trans hεU
    let ya := radialPoint p s.1 ρ
    let yb := radialPoint p s.2 ρ
    let Y : Finset V := {ya, yb}
    have hneY : ya ≠ yb := radialPoint_ne_of_mem_openSegment p s.1 s.2 hρpos hab hp_open
    have hYcard : Y.card = 2 := Finset.card_pair hneY
    have hYsph : ↑Y ⊆ sphere p ρ := by
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact mem_sphere_radialPoint p s.1 hρpos.le hne1
      · rw [Finset.mem_singleton.mp hy]; exact mem_sphere_radialPoint p s.2 hρpos.le hne2
    have hYrange : ↑Y ⊆ range (D.toDrawing.edgePath e) := by
      intro y hy
      have hseg_sub : segment ℝ s.1 s.2 ⊆ range (D.toDrawing.edgePath e) := by
        rw [D.range_edgePath e]; exact (D.cell e).segment_subset_toSet hs
      have hqseg : p ∈ segment ℝ s.1 s.2 := openSegment_subset_segment ℝ s.1 s.2 hp_open
      rcases Finset.mem_insert.mp hy with rfl | hy
      · have hrad := radialPoint_mem_segment p s.1 hρpos.le hρ_le_a
        have h1 : segment ℝ p ya ⊆ segment ℝ p s.1 :=
          (convex_segment p s.1).segment_subset (left_mem_segment _ _ _) hrad
        have hsub : segment ℝ p ya ⊆ segment ℝ s.1 s.2 :=
          h1.trans (by
            rw [← segment_union_eq_segment hqseg, segment_symm]
            exact subset_union_left)
        exact hseg_sub (hsub (right_mem_segment _ _ _))
      · rw [Finset.mem_singleton.mp hy]
        have hrad := radialPoint_mem_segment p s.2 hρpos.le hρ_le_b
        have h1 : segment ℝ p yb ⊆ segment ℝ p s.2 :=
          (convex_segment p s.2).segment_subset (left_mem_segment _ _ _) hrad
        have hsub : segment ℝ p yb ⊆ segment ℝ s.1 s.2 :=
          h1.trans (by
            rw [← segment_union_eq_segment hqseg]
            exact subset_union_right)
        exact hseg_sub (hsub (right_mem_segment _ _ _))
    refine ⟨ρ, hρpos, Y, hYsph, hYcard, hYrange, ?_⟩
    have hloc : closedBall p ρ ∩ D.toDrawing.support =
        closedBall p ρ ∩ segment ℝ s.1 s.2 := by
      ext x
      constructor
      · intro ⟨hxball, hxsup⟩
        have : x ∈ U ∩ D.toDrawing.support := ⟨hball_U hxball, hxsup⟩
        rw [hUeq] at this; exact ⟨hxball, this.2⟩
      · intro ⟨hxball, hxseg⟩
        have : x ∈ U ∩ segment ℝ s.1 s.2 := ⟨hball_U hxball, hxseg⟩
        rw [← hUeq] at this; exact ⟨hxball, this.2⟩
    have hYunion : (⋃ y ∈ Y, segment ℝ p y) = segment ℝ p ya ∪ segment ℝ p yb := by
      simp [Y]
    rw [hloc, closedBall_inter_segment_eq_two_radii p s.1 s.2 hρpos hab hp_open hρ_le_a hρ_le_b,
      two_radii_union_eq_star p ya yb, ← hYunion]

private lemma pathInterior_edgePath_eq_toSet_sdiff (D : PLDrawing G V) (e : E(G)) :
    pathInterior (D.toDrawing.edgePath e) =
      (D.cell e).toSet \
        ({D.toDrawing.vertex (edgeSource e), D.toDrawing.vertex (edgeTarget e)} : Set V) := by
  rw [← D.range_edgePath e]
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨⟨t, rfl⟩, ?_⟩
    rintro (h | h)
    · exact (Drawing.pathInterior_edgePath_disjoint_vertex D.toDrawing e).notMem_of_mem_left
        ⟨t, ht, rfl⟩ ⟨_, h.symm⟩
    · exact (Drawing.pathInterior_edgePath_disjoint_vertex D.toDrawing e).notMem_of_mem_left
        ⟨t, ht, rfl⟩ ⟨_, h.symm⟩
  · rintro ⟨⟨t, rfl⟩, hx⟩
    refine ⟨t, ⟨?_, ?_⟩, rfl⟩
    · exact lt_of_le_of_ne t.2.1 fun h0 ↦ hx <| Or.inl <| by
        rw [← h0]; simp [Path.source]
    · exact lt_of_le_of_ne t.2.2 fun h1 ↦ hx <| Or.inr <| by
        rw [h1]; simp [Path.target]

private lemma cell_length_pos (D : PLDrawing G V) (e : E(G)) : 0 < (D.cell e).length := by
  rcases D.cell_isSimpleArcOrLoop e with ⟨_, hlen⟩ | ⟨heq, hL⟩
  · exact hlen
  · have := PolygonalPath.IsSimpleLoop.length_pos (P := (D.cell e).cast rfl heq) hL
    rwa [PolygonalPath.cast_length] at this

private lemma cell_out_ne_source (D : PLDrawing G V) (e : E(G)) {b : V}
    (hb : (D.toDrawing.vertex (edgeSource e), b) ∈ (D.cell e).edges) :
    b ≠ D.toDrawing.vertex (edgeSource e) := by
  rcases D.cell_isSimpleArcOrLoop e with ⟨hS, _⟩ | ⟨heq, hL⟩
  · exact (hS.hasNondegenerateEdges _ hb).symm
  · have hL' : ((D.cell e).cast rfl heq).IsSimpleLoop := hL
    have hb' : (D.toDrawing.vertex (edgeSource e), b) ∈ ((D.cell e).cast rfl heq).edges := by
      rwa [PolygonalPath.edges_cast]
    exact (PolygonalPath.IsSimpleLoop.hasNondegenerateEdges hL' _ hb').symm

private lemma cell_in_ne_target (D : PLDrawing G V) (e : E(G)) {a : V}
    (ha : (a, D.toDrawing.vertex (edgeTarget e)) ∈ (D.cell e).edges) :
    a ≠ D.toDrawing.vertex (edgeTarget e) := by
  rcases D.cell_isSimpleArcOrLoop e with ⟨hS, _⟩ | ⟨heq, hL⟩
  · exact hS.hasNondegenerateEdges _ ha
  · have hL' : ((D.cell e).cast rfl heq).IsSimpleLoop := hL
    have ha0 : (a, D.toDrawing.vertex (edgeTarget e)) ∈ ((D.cell e).cast rfl heq).edges := by
      rwa [PolygonalPath.edges_cast]
    have heq_pair : (a, D.toDrawing.vertex (edgeTarget e)) =
        (a, D.toDrawing.vertex (edgeSource e)) := congrArg _ heq
    have ha' : (a, D.toDrawing.vertex (edgeSource e)) ∈ ((D.cell e).cast rfl heq).edges :=
      heq_pair ▸ ha0
    have hne : a ≠ D.toDrawing.vertex (edgeSource e) :=
      PolygonalPath.IsSimpleLoop.hasNondegenerateEdges hL' _ ha'
    have heq_ne : (a ≠ D.toDrawing.vertex (edgeSource e)) =
        (a ≠ D.toDrawing.vertex (edgeTarget e)) := by rw [heq]
    exact heq_ne ▸ hne

private lemma degree_eq_ncard_source_add_target [G.Finite] (v : V(G)) :
    G.degree v.1 = {e : E(G) | edgeSource e = v}.ncard + {e : E(G) | edgeTarget e = v}.ncard := by
  classical
  have : G.LocallyFinite := inferInstance
  let Outs : Set (E(G)) := {e | edgeSource e = v}
  let Ins : Set (E(G)) := {e | edgeTarget e = v}
  let L : Set (E(G)) := {e | edgeSource e = v ∧ edgeTarget e = v}
  let S : Set (E(G)) := {e | edgeSource e = v ∧ edgeTarget e ≠ v}
  let T : Set (E(G)) := {e | edgeTarget e = v ∧ edgeSource e ≠ v}
  have hOuts : Outs = L ∪ S := by
    ext e
    exact ⟨by grind, fun h ↦ h.elim And.left And.left⟩
  have hIns : Ins = L ∪ T := by
    ext e
    exact ⟨by grind, fun h ↦ h.elim And.right And.left⟩
  have hLS : Disjoint L S := disjoint_left.mpr fun _ hL hS ↦ hS.2 hL.2
  have hLT : Disjoint L T := disjoint_left.mpr fun _ hL hT ↦ hT.2 hL.1
  have hST : Disjoint S T := disjoint_left.mpr fun _ hS hT ↦ hT.2 hS.1
  have hL : {e | G.IsLoopAt e v.1} = Subtype.val '' L := by
    ext e
    refine ⟨fun he ↦ ⟨⟨e, he.inc.edge_mem⟩, ?_, rfl⟩, fun ⟨e', ⟨hs, ht⟩, heq⟩ ↦ ?_⟩
    · have hlink := isLink_edgeSource_edgeTarget ⟨e, he.inc.edge_mem⟩
      obtain ⟨h1, h2⟩ := he.eq_of_isLink hlink
      exact ⟨Subtype.ext h1.symm, Subtype.ext h2.symm⟩
    · have hlink := isLink_edgeSource_edgeTarget e'
      rw [hs, ht] at hlink
      exact isLink_self_iff.mp <| heq ▸ hlink
  have hN : {e | G.IsNonloopAt e v.1} = Subtype.val '' (S ∪ T) := by
    ext e; constructor
    · intro he
      have heE : e ∈ E(G) := he.inc.edge_mem
      refine ⟨⟨e, heE⟩, ?_, rfl⟩
      have hlink := isLink_edgeSource_edgeTarget ⟨e, heE⟩
      have hne_ends : edgeSource ⟨e, heE⟩ ≠ edgeTarget ⟨e, heE⟩ :=
        IsNonloopAt.edgeSource_ne_edgeTarget (e := ⟨e, heE⟩) (x := v) he
      have hends : edgeSource ⟨e, heE⟩ = v ∨ edgeTarget ⟨e, heE⟩ = v := by
        obtain ⟨y, hl⟩ := he.inc
        rcases hl.eq_and_eq_or_eq_and_eq hlink with ⟨h1, _⟩ | ⟨h1, _⟩
        · exact Or.inl (Subtype.ext h1.symm)
        · exact Or.inr (Subtype.ext h1.symm)
      rcases hends with hs | ht
      · exact Or.inl ⟨hs, fun h ↦ hne_ends (hs.trans h.symm)⟩
      · exact Or.inr ⟨ht, fun h ↦ hne_ends (h.trans ht.symm)⟩
    · rintro ⟨e', hST', rfl⟩
      refine (isNonloopAt_iff_inc_not_isLoopAt).mpr ?_
      have hlink := isLink_edgeSource_edgeTarget e'
      rcases hST' with ⟨hs, hne⟩ | ⟨ht, hne⟩
      · rw [hs] at hlink
        exact ⟨hlink.inc_left,
          fun hloop ↦ hne (Subtype.ext (IsLoopAt.eq_of_isLink hloop hlink).2.symm)⟩
      · rw [ht] at hlink
        exact ⟨hlink.inc_right,
          fun hloop ↦ hne (Subtype.ext (IsLoopAt.eq_of_isLink hloop hlink).1.symm)⟩
  rw [degree_eq_ncard_add_ncard, hL, hN,
    ncard_image_of_injective _ Subtype.val_injective,
    ncard_image_of_injective _ Subtype.val_injective]
  change 2 * L.ncard + (S ∪ T).ncard = Outs.ncard + Ins.ncard
  rw [hOuts, hIns, ncard_union_eq hLS, ncard_union_eq hLT, ncard_union_eq hST]
  ring

/-! ### Ends at a vertex

The packaging the degree conjunct of `exists_radius_vertex` needs. The earlier handoff asked for a
family `U : Ends → Set V` of *cells*, with four hypotheses to discharge, and bounced on two of them:
the `Fintype`/`ncard` wiring, and the shrink needed to make distinct pieces meet only at `p`.

Both dissolve if the piece is the **first (or last) segment of the cell** rather than the whole
cell. Then `U i = segment p (endTip i)` and:

* `U i ⊆ support` — a segment of a cell is in the support, no shrink;
* `∃ w ≠ p, segment p w ⊆ U i` — trivial, `w := endTip i`;
* `i ≠ j → U i ∩ U j ⊆ {p}` — **globally true**, no shrink: two end segments at `v` from different
  edges have interiors in disjoint open cells, and the two end segments of a loop meet only at `v`
  because a simple loop has length `≥ 3` and so is not a digon;
* `U i ∩ closedBall p ρ ⊆ segment p (z i)` — trivial with `z i := endTip i`.

Only the cover needs a small `ρ`, and that is the single lemma
`exists_radius_support_subset_iUnion_segment_endTip` below. `U` itself never appears: the two
`SegmentFigure` bounds are applied with `U i := segment ℝ p (endTip i)` directly. -/

/-- The **ends at `v`**: one for each edge with `edgeSource e = v`, one for each with
`edgeTarget e = v`. A loop at `v` contributes both, which is exactly why the count is `G.degree v`
rather than the number of incident edges. -/
abbrev EndsAt (G : Graph α β) (v : V(G)) : Type _ :=
  {e : E(G) // edgeSource e = v} ⊕ {e : E(G) // edgeTarget e = v}

/-- **The count.** This is the `Fintype`/`ncard` bridge the earlier attempt bounced on.

Stated with `Nat.card`, not `Fintype.card`: `E(G)` is a `Set`, so `[G.Finite]` supplies `Finite`
and *not* `Fintype`, and asking for `Fintype` here is what made the wiring fight back. `Nat.card`
needs no instance and is definitionally what `Set.ncard` already is, so
`degree_eq_ncard_source_add_target` lands with no conversion.

Route: `Nat.card_sum` splits the sum type, then `Set.Nat.card_coe_set_eq` rewrites each summand as
the `Set.ncard` appearing in `degree_eq_ncard_source_add_target`. Keep everything in `ℕ`; do not
detour through `eDegree`, which is `ℕ∞` and forces `ENat.toNat` juggling.

At the call site, `le_card_radii_of_pairwise` wants `[Fintype ι]`: obtain it with
`have : Finite (EndsAt G v) := inferInstance; letI := Fintype.ofFinite (EndsAt G v)` and bridge
back with `Nat.card_eq_fintype_card`. -/
lemma card_endsAt [G.Finite] (v : V(G)) : Nat.card (EndsAt G v) = G.degree v.1 := by
  rw [Nat.card_sum]
  change Nat.card ↑{e : E(G) | edgeSource e = v} + Nat.card ↑{e : E(G) | edgeTarget e = v} =
    G.degree v.1
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, degree_eq_ncard_source_add_target]

/-- The far endpoint of the cell segment at `v` belonging to an end: the first segment of the cell
for an out-end, the last for an in-end. Total, via `cell_length_pos`. -/
noncomputable def endTip (D : PLDrawing G V) {v : V(G)} : EndsAt G v → V
  | .inl e => Classical.choose (PolygonalPath.exists_edge_starting_at_first (D.cell_length_pos e.1))
  | .inr e => Classical.choose (PolygonalPath.exists_edge_ending_at_last (D.cell_length_pos e.1))

private lemma endTip_mem_edges_out (D : PLDrawing G V) {v : V(G)} (e : {e : E(G) // edgeSource e = v}) :
    (D.toDrawing.vertex v, D.endTip (.inl e)) ∈ (D.cell e.1).edges := by
  have hb := Classical.choose_spec
    (PolygonalPath.exists_edge_starting_at_first (D.cell_length_pos e.1))
  simpa [endTip, e.2] using hb

private lemma endTip_mem_edges_in (D : PLDrawing G V) {v : V(G)} (e : {e : E(G) // edgeTarget e = v}) :
    (D.endTip (.inr e), D.toDrawing.vertex v) ∈ (D.cell e.1).edges := by
  have ha := Classical.choose_spec
    (PolygonalPath.exists_edge_ending_at_last (D.cell_length_pos e.1))
  simpa [endTip, e.2] using ha

/- Route: unfold `endTip` to `Classical.choose_spec`, giving the cell edge, then
`cell_out_ne_source` for `.inl` and `cell_in_ne_target` for `.inr`. The `e.2` rewrite is what turns
`D.toDrawing.vertex (edgeSource e.1)` into `D.toDrawing.vertex v`. -/
lemma endTip_ne (D : PLDrawing G V) {v : V(G)} (i : EndsAt G v) :
    D.endTip i ≠ D.toDrawing.vertex v := by
  match i with
  | .inl e =>
    have hb := Classical.choose_spec
      (PolygonalPath.exists_edge_starting_at_first (D.cell_length_pos e.1))
    simpa [endTip, e.2] using cell_out_ne_source D e.1 hb
  | .inr e =>
    have ha := Classical.choose_spec
      (PolygonalPath.exists_edge_ending_at_last (D.cell_length_pos e.1))
    simpa [endTip, e.2] using cell_in_ne_target D e.1 ha

/- Route: `Classical.choose_spec` puts the pair in `(D.cell _).edges`, then
`PolygonalPath.segment_subset_toSet` lands it in the cell, and `D.range_edgePath` /
`Drawing.support_eq` land the cell in the support. -/
lemma segment_endTip_subset_support (D : PLDrawing G V) {v : V(G)} (i : EndsAt G v) :
    segment ℝ (D.toDrawing.vertex v) (D.endTip i) ⊆ D.toDrawing.support := by
  match i with
  | .inl e =>
    intro x hx
    have hcell : x ∈ (D.cell e.1).toSet :=
      (D.cell e.1).segment_subset_toSet (endTip_mem_edges_out D e) hx
    rw [Drawing.support_eq]
    refine Or.inr (mem_iUnion.mpr ⟨e.1, ?_⟩)
    rwa [D.range_edgePath]
  | .inr e =>
    intro x hx
    have hx' : x ∈ segment ℝ (D.endTip (.inr e)) (D.toDrawing.vertex v) := by
      rwa [segment_symm]
    have hcell : x ∈ (D.cell e.1).toSet :=
      (D.cell e.1).segment_subset_toSet (endTip_mem_edges_in D e) hx'
    rw [Drawing.support_eq]
    refine Or.inr (mem_iUnion.mpr ⟨e.1, ?_⟩)
    rwa [D.range_edgePath]

private def endEdge {v : V(G)} : EndsAt G v → E(G)
  | .inl e => e.1
  | .inr e => e.1

private lemma cell_isSimple_of_source_ne_target (D : PLDrawing G V) (e : E(G))
    (hne : edgeSource e ≠ edgeTarget e) : (D.cell e).IsSimple :=
  (PolygonalPath.isSimpleArcOrLoop_iff_isSimple
    (D.toDrawing.vertex_injective.ne hne)).mp (D.cell_isSimpleArcOrLoop e)

/-- The open end segment at `v`, excluding the tip, lies in the open cell. -/
private lemma openSegment_endTip_subset_pathInterior (D : PLDrawing G V) {v : V(G)}
    (i : EndsAt G v) :
    openSegment ℝ (D.toDrawing.vertex v) (D.endTip i) ⊆
      pathInterior (D.toDrawing.edgePath (endEdge i)) := by
  intro x hx
  have htipne : D.endTip i ≠ D.toDrawing.vertex v := endTip_ne D i
  have hx_ne_p : x ≠ D.toDrawing.vertex v := fun h ↦
    htipne.symm (left_mem_openSegment_iff.mp (h ▸ hx))
  have hxseg : x ∈ segment ℝ (D.toDrawing.vertex v) (D.endTip i) :=
    openSegment_subset_segment ℝ _ _ hx
  match i with
  | .inl e =>
    have hcell : x ∈ (D.cell e.1).toSet :=
      (D.cell e.1).segment_subset_toSet (endTip_mem_edges_out D e) hxseg
    have hx_ne_tgt : x ≠ D.toDrawing.vertex (edgeTarget e.1) := by
      intro ht
      by_cases hse : edgeSource e.1 = edgeTarget e.1
      · exact hx_ne_p (ht.trans (by rw [← hse, e.2]))
      · have hS := cell_isSimple_of_source_ne_target D e.1 hse
        have hmem := (hS.mem_segment_iff_of_mem_vertices
          (D.cell e.1).last_mem_vertices (endTip_mem_edges_out D e)).mp (ht ▸ hxseg)
        rcases hmem with htp | htt
        · exact hx_ne_p (ht.trans htp)
        · have hx_tip : x = D.endTip (.inl e) := ht.trans htt
          exact htipne (right_mem_openSegment_iff.mp (hx_tip ▸ hx)).symm
    rw [pathInterior_edgePath_eq_toSet_sdiff]
    refine ⟨hcell, ?_⟩
    rintro (hs | ht)
    · exact hx_ne_p (hs.trans (congrArg _ e.2))
    · exact hx_ne_tgt ht
  | .inr e =>
    have hx' : x ∈ segment ℝ (D.endTip (.inr e)) (D.toDrawing.vertex v) := by
      rwa [segment_symm]
    have hcell : x ∈ (D.cell e.1).toSet :=
      (D.cell e.1).segment_subset_toSet (endTip_mem_edges_in D e) hx'
    have hx_ne_src : x ≠ D.toDrawing.vertex (edgeSource e.1) := by
      intro hs
      by_cases hse : edgeSource e.1 = edgeTarget e.1
      · exact hx_ne_p (hs.trans (by rw [hse, e.2]))
      · have hS := cell_isSimple_of_source_ne_target D e.1 hse
        have hmem := (hS.mem_segment_iff_of_mem_vertices
          (D.cell e.1).first_mem_vertices (endTip_mem_edges_in D e)).mp (hs ▸ hx')
        rcases hmem with hts | htp
        · have hx_tip : x = D.endTip (.inr e) := hs.trans hts
          exact htipne (right_mem_openSegment_iff.mp (hx_tip ▸ hx)).symm
        · exact hx_ne_p (hs.trans htp)
    rw [pathInterior_edgePath_eq_toSet_sdiff]
    refine ⟨hcell, ?_⟩
    rintro (hs | ht)
    · exact hx_ne_src hs
    · exact hx_ne_p (ht.trans (congrArg _ e.2))

private lemma tip_mem_cell_toSet (D : PLDrawing G V) {v : V(G)} (i : EndsAt G v) :
    D.endTip i ∈ (D.cell (endEdge i)).toSet := by
  match i with
  | .inl e =>
    exact (D.cell e.1).segment_subset_toSet (endTip_mem_edges_out D e)
      (right_mem_segment _ _ _)
  | .inr e =>
    exact (D.cell e.1).segment_subset_toSet (endTip_mem_edges_in D e)
      (left_mem_segment _ _ _)

/-- The two end segments of a loop cell at `v` meet only at `v`.

Route: cast the cell to a based loop at `p := vertex v` (`source = target = v`), apply
`IsSimpleLoop.three_le_length` so the path is not a digon, then `isSimpleLoop_cons_iff` gives
`segment p tipOut ∩ Q.toSet ⊆ {p, tipOut}` with `Q` the tail after the first edge. The in-tip edge
`(tipIn, p)` lies in `Q.edges` (it is not the first edge, by `endTip_ne`), so
`segment tipIn p ⊆ Q.toSet`. Hence the intersection of the two end segments is in `{p, tipOut}`; the
`tipOut` case forces `tipOut = tipIn` via `mem_segment_iff_of_mem_vertices`, contradicting
`three_le_length` (digon). Identifying `tipOut` with the `cons` head uses that a simple path has no
edge starting at its last vertex (`mem_edges_iff` + `Nodup.getElem_inj_iff`).

**Stuck (tactic, not FH).** All named APIs exist. Failures were mechanical:
* `PolygonalPath.cast` / `edges_cast` / `isSimpleArcOrLoop_cast` vs `endTip` defined on the uncast
  cell — `simpa` on `(endTip (.inr f), p) ∈ P.edges` fights `f.1 = e.1` and `vertex v` vs `p`.
* Proving `endTip (.inl e) = b` for `P = cons p b Q`: the `List.mem_cons` right branch (edge
  starting at `p` inside `Q`) needs `Nodup` of `Q.vertices` plus “no outgoing edge from the last
  vertex”; `getLast`/`getElem` index arithmetic and `nodup_iff_injective_getElem` (Fin-shaped)
  repeatedly misfired.
* `tips_ne : tipIn ≠ tipOut` via `eq_first_edge_of_mem_segment` on `Q` when assuming `tipIn = b`
  works for `Q = direct b p` (`length = 2` vs `three_le_length`), but the longer-`Q` revisit-`p`
  case needs a clean `vertices.Nodup` contradiction after subst.

No missing public lemma: a short private `endTip_eq_cons_head` / `no_edge_starting_at_last` would
be local sugar, not scaffolding. -/
private lemma segment_endTip_inter_loop (D : PLDrawing G V) {v : V(G)}
    (e : {e : E(G) // edgeSource e = v}) (f : {e : E(G) // edgeTarget e = v})
    (hef : e.1 = f.1) :
    segment ℝ (D.toDrawing.vertex v) (D.endTip (.inl e)) ∩
        segment ℝ (D.toDrawing.vertex v) (D.endTip (.inr f)) ⊆
      {D.toDrawing.vertex v} := by
  sorry

/-- **Distinct ends give segments meeting only at `v`** — with no shrinking, which is the point. -/
lemma segment_endTip_inter (D : PLDrawing G V) {v : V(G)} {i j : EndsAt G v} (hij : i ≠ j) :
    segment ℝ (D.toDrawing.vertex v) (D.endTip i) ∩ segment ℝ (D.toDrawing.vertex v) (D.endTip j)
      ⊆ {D.toDrawing.vertex v} := by
  intro x ⟨hxi, hxj⟩
  set p := D.toDrawing.vertex v
  by_contra hx_not
  have hxne : x ≠ p := fun h ↦ hx_not (h ▸ rfl)
  have tip_or_open (k : EndsAt G v) (hxk : x ∈ segment ℝ p (D.endTip k)) :
      x = D.endTip k ∨ x ∈ pathInterior (D.toDrawing.edgePath (endEdge k)) := by
    by_cases ht : x = D.endTip k
    · exact Or.inl ht
    · exact Or.inr <| openSegment_endTip_subset_pathInterior D k <|
        mem_openSegment_of_ne_left_right hxne.symm (mt Eq.symm ht) hxk
  have tip_endpoint_or_interior (k : EndsAt G v) :
      D.endTip k = D.toDrawing.vertex (edgeSource (endEdge k)) ∨
        D.endTip k = D.toDrawing.vertex (edgeTarget (endEdge k)) ∨
        D.endTip k ∈ pathInterior (D.toDrawing.edgePath (endEdge k)) := by
    by_cases hs : D.endTip k = D.toDrawing.vertex (edgeSource (endEdge k))
    · exact Or.inl hs
    · by_cases ht : D.endTip k = D.toDrawing.vertex (edgeTarget (endEdge k))
      · exact Or.inr (Or.inl ht)
      · refine Or.inr (Or.inr ?_)
        rw [pathInterior_edgePath_eq_toSet_sdiff]
        exact ⟨tip_mem_cell_toSet D k, fun h ↦ h.elim hs ht⟩
  by_cases hedf : endEdge i = endEdge j
  · match i, j with
    | .inl e, .inl f =>
      exact (hij (congrArg Sum.inl (Subtype.ext hedf))).elim
    | .inr e, .inr f =>
      exact (hij (congrArg Sum.inr (Subtype.ext hedf))).elim
    | .inl e, .inr f =>
      exact hx_not (segment_endTip_inter_loop D e f hedf ⟨hxi, hxj⟩)
    | .inr e, .inl f =>
      exact hx_not (segment_endTip_inter_loop D f e hedf.symm ⟨hxj, hxi⟩)
  · have hi := tip_or_open i hxi
    have hj := tip_or_open j hxj
    have tip_meets_open (k ℓ : EndsAt G v) (hkℓ : endEdge k ≠ endEdge ℓ)
        (htip : x = D.endTip k)
        (hopen : x ∈ pathInterior (D.toDrawing.edgePath (endEdge ℓ))) : False := by
      have hxℓ : D.endTip k ∈ pathInterior (D.toDrawing.edgePath (endEdge ℓ)) := by
        rwa [← htip]
      rcases tip_endpoint_or_interior k with hk | hk | hk
      · exact (Drawing.pathInterior_edgePath_disjoint_vertex D.toDrawing (endEdge ℓ)).notMem_of_mem_left
          hxℓ ⟨edgeSource (endEdge k), hk.symm⟩
      · exact (Drawing.pathInterior_edgePath_disjoint_vertex D.toDrawing (endEdge ℓ)).notMem_of_mem_left
          hxℓ ⟨edgeTarget (endEdge k), hk.symm⟩
      · exact (Drawing.pathInterior_edgePath_disjoint D.toDrawing hkℓ).notMem_of_mem_left hk hxℓ
    rcases hi with hi | hi
    · rcases hj with hj | hj
      · have eqt : D.endTip i = D.endTip j := hi.symm.trans hj
        have hmi : midpoint ℝ p (D.endTip i) ∈
            pathInterior (D.toDrawing.edgePath (endEdge i)) :=
          openSegment_endTip_subset_pathInterior D i (midpoint_mem_openSegment _ _)
        have hmj : midpoint ℝ p (D.endTip i) ∈
            pathInterior (D.toDrawing.edgePath (endEdge j)) := by
          rw [eqt]
          exact openSegment_endTip_subset_pathInterior D j (midpoint_mem_openSegment _ _)
        exact (Drawing.pathInterior_edgePath_disjoint D.toDrawing hedf).notMem_of_mem_left hmi hmj
      · exact tip_meets_open i j hedf hi hj
    · rcases hj with hj | hj
      · exact tip_meets_open j i (Ne.symm hedf) hj hi
      · exact (Drawing.pathInterior_edgePath_disjoint D.toDrawing hedf).notMem_of_mem_left hi hj

/-- **The cover, and the only place a small radius is needed.** Near `v` the drawing is exactly the
union of the end segments.

Route: `exists_finite_support` writes the support as `range vertex ∪ ⋃ s ∈ S, segment s.1 s.2` with
`S` finite. Bound `ρ` below all of:
* `dist (vertex v) w` for the finitely many other vertex images `w`;
* the distance from `vertex v` to each segment of `S` not containing it;
* half the distance from `vertex v` to each `endTip i`.

Then a point of the support in `closedBall (vertex v) ρ` other than `vertex v` lies on a segment
through `vertex v`; that segment is an edge of some cell at `v`, and
`eq_first_edge_of_mem_segment` / `eq_last_edge_of_mem_segment` identify it as an end segment.

Alternative: for each non-loop out-end apply `exists_ball_inter_subset_firstSegment` (and reverse for
in-ends); for a loop take the min of the two one-sided radii from `isSimpleLoop_cons_iff`; then min
against the distance to non-incident cells.

**Stuck (tactic, not FH).** Packaging and named lemmas are enough; assembly of
`exists_radius_vertex` already consumes this statement. Failures:
* Finite-support route: δ-bound against `K = (range vertex \ {p}) ∪ ⋃ Srest` copies
  `IsSegmentFigure.exists_radius` cleanly; the hard step is identifying a segment through `p` as
  `segment p (endTip i)`. That needs `endTip_eq` from “`(p, b)` (resp. `(b, p)`) is the first
  (resp. last) edge of the cell”, which is the same uniqueness stuck point as
  `segment_endTip_inter_loop`.
* Per-end `exists_ball_inter_subset_firstSegment` route: the existential `z` is *some* point with
  `cell ∩ ball ⊆ segment p z`, not definitionally `endTip`. Closing `segment p z ⊆ segment p
  (endTip i)` (or proving `z = endTip`) again needs first-edge uniqueness. Loops are excluded by
  that lemma’s `x ≠ y`, so they need a separate two-sided radius anyway.

Preferred next cut: prove private `endTip_inl_eq` / `endTip_inr_eq` (first/last edge determines the
tip) once, then both this cover and the loop intersection become short. -/
theorem exists_radius_support_subset_iUnion_segment_endTip [G.Finite] (D : PLDrawing G V)
    (v : V(G)) :
    ∃ ρ > 0, D.toDrawing.support ∩ closedBall (D.toDrawing.vertex v) ρ ⊆
      {D.toDrawing.vertex v} ∪ ⋃ i : EndsAt G v, segment ℝ (D.toDrawing.vertex v) (D.endTip i) := by
  sorry

/-- At a vertex there is one radius per edge end: `degree` counts a loop twice, and a loop does
contribute two radii. -/
theorem exists_radius_vertex [G.Finite] (D : PLDrawing G V) (v : V(G)) :
    ∃ ρ > 0, ∃ Y : Finset V, ↑Y ⊆ sphere (D.toDrawing.vertex v) ρ ∧
      (Y.card : ℕ∞) = G.degree v.1 ∧
      closedBall (D.toDrawing.vertex v) ρ ∩ D.toDrawing.support =
        {D.toDrawing.vertex v} ∪ ⋃ y ∈ Y, segment ℝ (D.toDrawing.vertex v) y := by
  classical
  set p := D.toDrawing.vertex v
  obtain ⟨ρ₀, hρ₀, Y₀, hY₀, hstar₀⟩ := D.exists_radius (Drawing.vertex_mem_support _ v)
  obtain ⟨ρ₁, hρ₁, hcover₁⟩ := D.exists_radius_support_subset_iUnion_segment_endTip v
  let ρ : ℝ := min ρ₀ ρ₁
  have hρ : 0 < ρ := lt_min hρ₀ hρ₁
  obtain ⟨Y, hY, -, hstar⟩ :=
    exists_radius_of_le hρ₀ hY₀ hstar₀ hρ (min_le_left _ _)
  refine ⟨ρ, hρ, Y, hY, ?_, hstar⟩
  have : Finite (EndsAt G v) := inferInstance
  letI : Fintype (EndsAt G v) := Fintype.ofFinite _
  let U : EndsAt G v → Set V := fun i ↦ segment ℝ p (D.endTip i)
  have hge : Fintype.card (EndsAt G v) ≤ Y.card :=
    le_card_radii_of_pairwise (T := D.toDrawing.support) hρ hY hstar
      (fun i ↦ segment_endTip_subset_support D i)
      (fun i ↦ ⟨D.endTip i, endTip_ne D i, subset_rfl⟩)
      (fun i j hij ↦ segment_endTip_inter D hij)
  have hcover : D.toDrawing.support ∩ closedBall p ρ ⊆ {p} ∪ ⋃ i, U i := by
    intro x hx
    exact hcover₁ ⟨hx.1, closedBall_subset_closedBall (min_le_right ρ₀ ρ₁) hx.2⟩
  have hle : Y.card ≤ Fintype.card (EndsAt G v) :=
    card_radii_le_of_cover (T := D.toDrawing.support) hρ hY hstar hcover (endTip_ne D)
      (fun _ ↦ Set.inter_subset_left)
  have hEq : Y.card = Nat.card (EndsAt G v) := by
    rw [Nat.card_eq_fintype_card]
    exact Nat.le_antisymm hle hge
  rw [hEq, card_endsAt]

/- **Assembly of the degree conjunct** (formalisation helper). Every piece is now named; this is the
order to put them in. Write `p := D.toDrawing.vertex v` and `U i := segment ℝ p (D.endTip i)`.

1. `exists_radius_support_subset_iUnion_segment_endTip` gives `ρ₁ > 0` for the cover. Take
   `ρ := min ρ₀ ρ₁` with `ρ₀` from `exists_radius`, then transport the star down with
   `exists_radius_of_le` — which keeps `Y.card`, so nothing about `Y` is lost. **The `refine` above
   must therefore be reorganised**: pick the radius *before* introducing `Y`, rather than taking
   whatever `exists_radius` returned.
2. `letI := Fintype.ofFinite (EndsAt G v)` (see `card_endsAt` for why `Finite` is all that
   `[G.Finite]` gives here).
3. `Y.card ≥` : `le_card_radii_of_pairwise` with `hUT := segment_endTip_subset_support`,
   `hUp := fun i ↦ ⟨D.endTip i, endTip_ne D i, subset_rfl⟩`, `hmeet := segment_endTip_inter`.
   Note none of these three needs the radius — that is the whole point of taking `U i` to be the
   end *segment* rather than the cell.
4. `Y.card ≤` : `card_radii_le_of_cover` with `z := D.endTip`, `hzne := endTip_ne D`,
   `hcover` from step 1, and `hUz := fun i ↦ Set.inter_subset_left`.
5. `Nat.le_antisymm` gives `Y.card = Nat.card (EndsAt G v)` (via `Nat.card_eq_fintype_card`), and
   `card_endsAt` rewrites it to `G.degree v.1`. Cast to `ℕ∞` last, with `Nat.cast_inj`.

The two `SegmentFigure` bounds are stated about *any* `Y` satisfying the star equation, so `Y` never
has to be unfolded — which is what defeated the earlier attempt. -/

/-! ### 3.7, accessibility -/

/-- **Accessibility.** A point on the frontier of a face can be joined to that face by a straight
segment leaving the drawing immediately. -/
theorem exists_segment_sdiff_subset_faceSet [G.Finite]
    (D : PLDrawing G (EuclideanSpace ℝ (Fin 2))) {p : EuclideanSpace ℝ (Fin 2)}
    (hp : p ∈ D.toDrawing.support) (F : D.toDrawing.onePoint.Face)
    (hpF : (p : OnePoint (EuclideanSpace ℝ (Fin 2))) ∈ frontier (D.toDrawing.onePoint.faceSet F)) :
    ∃ y : EuclideanSpace ℝ (Fin 2), y ≠ p ∧
      (↑) '' (segment ℝ p y \ {p}) ⊆ D.toDrawing.onePoint.faceSet F := by
  classical
  obtain ⟨ρ, hρ, Y, hY, hstar⟩ := D.exists_radius hp
  have hnhds :
      (↑) '' (ball p ρ) ∈ 𝓝 (p : OnePoint (EuclideanSpace ℝ (Fin 2))) := by
    rw [OnePoint.nhds_coe_eq]
    exact Filter.image_mem_map (ball_mem_nhds _ hρ)
  obtain ⟨z', ⟨hzU, hzF⟩⟩ :=
    mem_closure_iff_nhds.mp (frontier_subset_closure hpF) ((↑) '' ball p ρ) hnhds
  obtain ⟨z, hzball, rfl⟩ := hzU
  have hzS : z ∉ D.toDrawing.support := by
    have : (z : OnePoint (EuclideanSpace ℝ (Fin 2))) ∉ D.toDrawing.onePoint.support :=
      (D.toDrawing.onePoint.faceSet_disjoint_support F).notMem_of_mem_left hzF
    rw [Drawing.support_onePoint] at this
    exact fun hz ↦ this ⟨z, hz, rfl⟩
  have hzne : z ≠ p := fun h ↦ hzS (h ▸ hp)
  refine ⟨z, hzne, ?_⟩
  have hseg_off : segment ℝ p z \ {p} ⊆ D.toDrawing.supportᶜ := by
    intro w ⟨hwseg, hwp⟩ hwS
    have hwball : w ∈ closedBall p ρ :=
      ball_subset_closedBall <|
        (convex_ball p ρ).segment_subset (mem_ball_self hρ) hzball hwseg
    have hwstar : w ∈ ({p} ∪ ⋃ y ∈ Y, segment ℝ p y :
        Set (EuclideanSpace ℝ (Fin 2))) := by
      rw [← hstar]; exact ⟨hwball, hwS⟩
    rcases hwstar with rfl | hwY
    · exact hwp rfl
    · obtain ⟨y, hyY, hwy⟩ := mem_iUnion₂.mp hwY
      obtain ⟨t, ⟨ht0, _⟩, rfl⟩ := (segment_eq_image_lineMap (𝕜 := ℝ) p y).symm ▸ hwy
      obtain ⟨s, ⟨hs0, _⟩, hseq⟩ := (segment_eq_image_lineMap (𝕜 := ℝ) p z).symm ▸ hwseg
      have htpos : 0 < t :=
        lt_of_le_of_ne ht0 fun ht ↦ hwp (by simp [AffineMap.lineMap_apply, ht])
      have hspos : 0 < s :=
        lt_of_le_of_ne hs0 fun hs ↦ hwp <|
          hseq.symm.trans (by simp [AffineMap.lineMap_apply, hs])
      have hvec : t • (y - p) = s • (z - p) := by
        have h1 := congrArg (fun u : EuclideanSpace ℝ (Fin 2) ↦ u - p) hseq
        -- hseq : lineMap p z s = lineMap p y t, so s • (z-p) = t • (y-p)
        simp only [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub, add_sub_cancel_right] at h1
        exact h1.symm
      have hcoef_vec : z - p = (t / s) • (y - p) := by
        calc
          z - p = s⁻¹ • (s • (z - p)) := (inv_smul_smul₀ hspos.ne' _).symm
          _ = s⁻¹ • (t • (y - p)) := by rw [hvec]
          _ = (s⁻¹ * t) • (y - p) := by rw [smul_smul]
          _ = (t / s) • (y - p) := by rw [div_eq_mul_inv, mul_comm]
      have hz_eq : z = AffineMap.lineMap p y (t / s) := by
        rw [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub, ← hcoef_vec]
        abel
      have hty : dist p y = ρ := by
        simpa [PseudoMetricSpace.dist_comm] using mem_sphere.mp (hY hyY)
      have hdist : dist p z = (t / s) * dist p y := by
        rw [hz_eq, ← PseudoMetricSpace.dist_comm,
          dist_lineMap_left_of_nonneg p y (div_nonneg htpos.le hspos.le),
          PseudoMetricSpace.dist_comm]
      have hzt : dist p z < ρ := by
        simpa [PseudoMetricSpace.dist_comm] using mem_ball.mp hzball
      have hcoef : t / s ≤ 1 := by
        have hypos : 0 < dist p y := by rw [hty]; exact hρ
        have hlt : (t / s) * dist p y < dist p y := by
          calc
            (t / s) * dist p y = dist p z := hdist.symm
            _ < ρ := hzt
            _ = dist p y := hty.symm
        exact (mul_lt_iff_lt_one_left hypos).mp hlt |>.le
      have hzseg : z ∈ segment ℝ p y := by
        rw [hz_eq, segment_eq_image_lineMap]
        exact ⟨t / s, ⟨div_nonneg htpos.le hspos.le, hcoef⟩, rfl⟩
      have : z ∈ closedBall p ρ ∩ D.toDrawing.support := by
        rw [hstar]; exact Or.inr (mem_iUnion₂.mpr ⟨y, hyY, hzseg⟩)
      exact hzS this.2
  have hseg_eq : segment ℝ p z \ {p} = AffineMap.lineMap p z '' Ioc (0 : ℝ) 1 := by
    ext w
    simp only [mem_sdiff, mem_singleton_iff, mem_image, mem_Ioc, segment_eq_image_lineMap]
    constructor
    · rintro ⟨⟨t, ⟨ht0, ht1⟩, rfl⟩, hwp⟩
      refine ⟨t, ⟨lt_of_le_of_ne ht0 ?_, ht1⟩, rfl⟩
      exact fun ht ↦ hwp (by simp [AffineMap.lineMap_apply, ht])
    · rintro ⟨t, ⟨ht0, ht1⟩, rfl⟩
      refine ⟨⟨t, ⟨ht0.le, ht1⟩, rfl⟩, ?_⟩
      intro h
      have hsmul : t • (z - p) = 0 := by
        have := congrArg (fun u : EuclideanSpace ℝ (Fin 2) ↦ u - p) h
        simpa [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub] using this
      exact hzne (sub_eq_zero.mp ((smul_eq_zero.mp hsmul).resolve_left ht0.ne'))
  have hconn : IsConnected
      ((↑) '' (segment ℝ p z \ {p}) : Set (OnePoint (EuclideanSpace ℝ (Fin 2)))) := by
    rw [hseg_eq, ← image_comp]
    exact (isConnected_Ioc (show (0 : ℝ) < 1 by norm_num)).image _
      (OnePoint.continuous_coe.comp AffineMap.lineMap_continuous).continuousOn
  have himg : (↑) '' (segment ℝ p z \ {p}) ⊆ D.toDrawing.onePoint.supportᶜ := by
    intro w hw
    obtain ⟨w0, hw0, rfl⟩ := hw
    rw [Drawing.support_onePoint]
    exact fun ⟨w1, hw1, hqw⟩ ↦ hseg_off hw0 (OnePoint.coe_injective hqw ▸ hw1)
  have hz_mem : (z : OnePoint (EuclideanSpace ℝ (Fin 2))) ∈ (↑) '' (segment ℝ p z \ {p}) :=
    ⟨z, ⟨right_mem_segment ℝ p z, hzne⟩, rfl⟩
  rw [D.toDrawing.onePoint.faceSet_eq_connectedComponentIn F hzF]
  exact hconn.isPreconnected.subset_connectedComponentIn hz_mem himg

/-! ### 3.8, the two sides of an open cell -/

/-- The faces having a given point of an open cell on their frontier. -/
def facesAt (D : PLDrawing G (EuclideanSpace ℝ (Fin 2))) (p : EuclideanSpace ℝ (Fin 2)) :
    Set D.toDrawing.onePoint.Face :=
  {F | (p : OnePoint (EuclideanSpace ℝ (Fin 2))) ∈ frontier (D.toDrawing.onePoint.faceSet F)}

/-- Distinct faces have disjoint carriers. -/
/- Both lemmas in this block were graph-free and have moved to `ForMathlib`; what remains is the
transport into the drawing's `Face` type. `Drawing.Face` is *by definition*
`ConnectedComponents ↥(supportᶜ)` and `Drawing.faceSet` is *by definition* the corresponding image,
so neither statement ever needed a graph. See Kuratowski `Decisions.md` D14/D16. -/

private lemma faceSet_disjoint_of_ne {X : Type*} [TopologicalSpace X] {G : Graph α β}
    (D : Drawing G X) {F G' : D.Face} (hne : F ≠ G') :
    Disjoint (D.faceSet F) (D.faceSet G') :=
  disjoint_val_image_connectedComponents hne

/-- **Sector extraction.** If the closed ball at `p` meets the drawing in a star, then any face
whose frontier reaches a point `q` of the open ball contains the image of a whole sector of the
punctured disk.

Stated for a general `q ∈ ball p ρ` rather than for `p` itself: two of the three call sites want
`q = p` and the third does not, and the argument never looks at which.

This is `exists_sector_subset_connectedComponentIn` transported along
`Drawing.faceSet_eq_connectedComponentIn` and `Drawing.support_onePoint`. -/
private lemma exists_sector_subset_faceSet [G.Finite]
    (D : PLDrawing G (EuclideanSpace ℝ (Fin 2))) {p q : EuclideanSpace ℝ (Fin 2)}
    {ρ : ℝ} {Y : Finset (EuclideanSpace ℝ (Fin 2))} (hYne : Y.Nonempty)
    (hstar : closedBall p ρ ∩ D.toDrawing.support = {p} ∪ ⋃ y ∈ Y, segment ℝ p y)
    (hqball : q ∈ ball p ρ) {F : D.toDrawing.onePoint.Face} (hF : F ∈ D.facesAt q) :
    ∃ C ∈ sectors p ρ Y, (↑) '' C ⊆ D.toDrawing.onePoint.faceSet F := by
  obtain ⟨w, hw⟩ := D.toDrawing.onePoint.faceSet_nonempty F
  have hEq : D.toDrawing.onePoint.faceSet F
      = connectedComponentIn ((↑) '' D.toDrawing.support : Set (OnePoint _))ᶜ w := by
    rw [D.toDrawing.onePoint.faceSet_eq_connectedComponentIn F hw, Drawing.support_onePoint]
  rw [hEq]
  have hF' : (q : OnePoint (EuclideanSpace ℝ (Fin 2))) ∈
      frontier (D.toDrawing.onePoint.faceSet F) := hF
  exact exists_sector_subset_connectedComponentIn hYne hstar hqball (by rwa [hEq] at hF')


/-- An open cell has at most two sides. -/
theorem ncard_facesAt_le_two [G.Finite] (D : PLDrawing G (EuclideanSpace ℝ (Fin 2))) {e : E(G)}
    {p : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ pathInterior (D.toDrawing.edgePath e)) :
    (D.facesAt p).ncard ≤ 2 := by
  classical
  obtain ⟨ρ, hρ, Y, hYsph, hYcard, _, hstar⟩ := D.exists_radius_edgeInterior hp
  have hYne : Y.Nonempty := Finset.card_pos.mp (by omega)
  have hsec : (sectors p ρ Y).ncard = 2 := by
    rw [ncard_sectors hρ hYne hYsph, hYcard]
  have hex (F : D.toDrawing.onePoint.Face) (hF : F ∈ D.facesAt p) :
      ∃ C ∈ sectors p ρ Y, (↑) '' C ⊆ D.toDrawing.onePoint.faceSet F :=
    exists_sector_subset_faceSet D hYne hstar (mem_ball_self hρ) hF
  let C : D.toDrawing.onePoint.Face → Set (EuclideanSpace ℝ (Fin 2)) := fun F =>
    if h : F ∈ D.facesAt p then Classical.choose (hex F h) else ∅
  have hCsec (F : D.toDrawing.onePoint.Face) (hF : F ∈ D.facesAt p) :
      C F ∈ sectors p ρ Y := by
    simp only [C, dif_pos hF]
    exact (Classical.choose_spec (hex F hF)).1
  have hCface (F : D.toDrawing.onePoint.Face) (hF : F ∈ D.facesAt p) :
      (↑) '' (C F) ⊆ D.toDrawing.onePoint.faceSet F := by
    simp only [C, dif_pos hF]
    exact (Classical.choose_spec (hex F hF)).2
  have hinj : InjOn C (D.facesAt p) := by
    intro F hF G' hG hCG
    by_contra hne
    have hdisj := faceSet_disjoint_of_ne D.toDrawing.onePoint hne
    obtain ⟨w0, hw0⟩ := (isConnected_of_mem_sectors (hCsec F hF)).nonempty
    have hFmem : (w0 : OnePoint (EuclideanSpace ℝ (Fin 2))) ∈
        D.toDrawing.onePoint.faceSet F :=
      hCface F hF ⟨w0, hw0, rfl⟩
    have hGmem : (w0 : OnePoint (EuclideanSpace ℝ (Fin 2))) ∈
        D.toDrawing.onePoint.faceSet G' :=
      hCface G' hG ⟨w0, (hCG ▸ hw0), rfl⟩
    exact hdisj.notMem_of_mem_left hFmem hGmem

  have hfin : (sectors p ρ Y).Finite :=
    finite_of_ncard_ne_zero (by rw [hsec]; norm_num)
  exact (ncard_le_ncard_of_injOn C (fun F hF ↦ hCsec F hF) hinj hfin).trans hsec.le

/-- Faces meeting a two-radius star are exactly the faces that contain a sector. -/
private lemma facesAt_eq_image_sectors [G.Finite]
    (D : PLDrawing G (EuclideanSpace ℝ (Fin 2))) {p : EuclideanSpace ℝ (Fin 2)}
    {ρ : ℝ} {Y : Finset (EuclideanSpace ℝ (Fin 2))} (hρ : 0 < ρ)
    (hYsph : ↑Y ⊆ sphere p ρ) (hYcard : Y.card = 2)
    (hstar : closedBall p ρ ∩ D.toDrawing.support =
      {p} ∪ ⋃ y ∈ Y, segment ℝ p y)
    (hp : (p : OnePoint (EuclideanSpace ℝ (Fin 2))) ∈ D.toDrawing.onePoint.support) :
    D.facesAt p =
      {F : D.toDrawing.onePoint.Face |
        ∃ C ∈ sectors p ρ Y, (↑) '' C ⊆ D.toDrawing.onePoint.faceSet F} := by
  classical
  have hYne : Y.Nonempty := Finset.card_pos.mp (by omega)
  have hclsupp := D.toDrawing.isClosed_support_onePoint
  ext F
  constructor
  · exact fun hF ↦ exists_sector_subset_faceSet D hYne hstar (mem_ball_self hρ) hF
  · intro ⟨C, hC, hCface⟩
    have hp_cl :
        (p : OnePoint (EuclideanSpace ℝ (Fin 2))) ∈
          closure (D.toDrawing.onePoint.faceSet F) := by
      have hpC : p ∈ closure C := mem_closure_of_mem_sectors hρ hYne hYsph hC
      have himg_cl :
          (↑) '' closure C ⊆
            closure ((↑) '' C : Set (OnePoint (EuclideanSpace ℝ (Fin 2)))) :=
        image_closure_subset_closure_image OnePoint.continuous_coe
      have : (p : OnePoint (EuclideanSpace ℝ (Fin 2))) ∈
          closure ((↑) '' C : Set (OnePoint (EuclideanSpace ℝ (Fin 2)))) :=
        himg_cl ⟨p, hpC, rfl⟩
      exact closure_mono hCface this
    have hp_not :
        (p : OnePoint (EuclideanSpace ℝ (Fin 2))) ∉ D.toDrawing.onePoint.faceSet F :=
      (D.toDrawing.onePoint.faceSet_disjoint_support F).notMem_of_mem_right hp
    have hFopen := D.toDrawing.onePoint.faceSet_isOpen hclsupp F
    change _ ∈ frontier (D.toDrawing.onePoint.faceSet F)
    rw [hFopen.frontier_eq]
    exact ⟨hp_cl, hp_not⟩

/-- On a two-radius star ball, `facesAt` is constant along the open cell. -/
private lemma facesAt_eq_of_mem_star_ball [G.Finite]
    (D : PLDrawing G (EuclideanSpace ℝ (Fin 2))) {e : E(G)}
    {p q : EuclideanSpace ℝ (Fin 2)} {ρ : ℝ}
    {Y : Finset (EuclideanSpace ℝ (Fin 2))}
    (hp : p ∈ pathInterior (D.toDrawing.edgePath e))
    (hq : q ∈ pathInterior (D.toDrawing.edgePath e))
    (hρ : 0 < ρ) (hYsph : ↑Y ⊆ sphere p ρ) (hYcard : Y.card = 2)
    (hstar : closedBall p ρ ∩ D.toDrawing.support =
      {p} ∪ ⋃ y ∈ Y, segment ℝ p y)
    (hqball : q ∈ ball p ρ) :
    D.facesAt q = D.facesAt p := by
  classical
  have hYne : Y.Nonempty := Finset.card_pos.mp (by omega)
  have hp_sup : p ∈ D.toDrawing.support :=
    Drawing.edgePath_range_subset_support D.toDrawing e (pathInterior_subset_range _ hp)
  have hq_sup : q ∈ D.toDrawing.support :=
    Drawing.edgePath_range_subset_support D.toDrawing e (pathInterior_subset_range _ hq)
  have hp_one : (p : OnePoint (EuclideanSpace ℝ (Fin 2))) ∈ D.toDrawing.onePoint.support := by
    rw [Drawing.support_onePoint]; exact ⟨p, hp_sup, rfl⟩
  have hq_one : (q : OnePoint (EuclideanSpace ℝ (Fin 2))) ∈ D.toDrawing.onePoint.support := by
    rw [Drawing.support_onePoint]; exact ⟨q, hq_sup, rfl⟩
  have hfaces_p := facesAt_eq_image_sectors D hρ hYsph hYcard hstar hp_one
  by_cases hqp : q = p
  · subst hqp; rfl
  have hqrad : q ∈ ⋃ y ∈ Y, segment ℝ p y := by
    have hqstar : q ∈ ({p} ∪ ⋃ y ∈ Y, segment ℝ p y :
        Set (EuclideanSpace ℝ (Fin 2))) := by
      rw [← hstar]
      exact ⟨ball_subset_closedBall hqball, hq_sup⟩
    rcases hqstar with rfl | h
    · exact (hqp rfl).elim
    · exact h
  obtain ⟨y, hyY, hqseg⟩ := mem_iUnion₂.mp hqrad
  have hqy : q ≠ y := by
    intro h
    have hdist : dist p q = ρ := by
      simpa [h, PseudoMetricSpace.dist_comm] using mem_sphere.mp (hYsph hyY)
    have hdist' : dist q p = ρ := by rwa [PseudoMetricSpace.dist_comm]
    exact (mem_ball.mp hqball).ne hdist'
  have hadj : {C ∈ sectors p ρ Y | q ∈ closure C} = sectors p ρ Y := by
    have hn := ncard_sectors_closure_eq_two hρ hYsph (by omega) hyY
      ⟨hqseg, by simp [hqp, hqy]⟩
    have hall : (sectors p ρ Y).ncard = 2 := by
      rw [ncard_sectors hρ hYne hYsph, hYcard]
    have hsub : {C ∈ sectors p ρ Y | q ∈ closure C} ⊆ sectors p ρ Y := sep_subset _ _
    have hfin : (sectors p ρ Y).Finite :=
      finite_of_ncard_ne_zero (by rw [hall]; norm_num)
    exact eq_of_subset_of_ncard_le hsub (by rw [hn, hall]) hfin
  have hsec_eq :
      D.facesAt q =
        {F : D.toDrawing.onePoint.Face |
          ∃ C ∈ sectors p ρ Y, (↑) '' C ⊆ D.toDrawing.onePoint.faceSet F} := by
    ext F
    constructor
    · exact fun hF ↦ exists_sector_subset_faceSet D hYne hstar hqball hF
    · intro ⟨C, hC, hCface⟩
      have hCadj : q ∈ closure C := by
        have : C ∈ {C ∈ sectors p ρ Y | q ∈ closure C} := by
          rw [hadj]; exact hC
        exact this.2
      have hclsupp := D.toDrawing.isClosed_support_onePoint
      have hq_cl :
          (q : OnePoint (EuclideanSpace ℝ (Fin 2))) ∈
            closure (D.toDrawing.onePoint.faceSet F) := by
        have himg_cl :
            (↑) '' closure C ⊆
              closure ((↑) '' C : Set (OnePoint (EuclideanSpace ℝ (Fin 2)))) :=
          image_closure_subset_closure_image OnePoint.continuous_coe
        have : (q : OnePoint (EuclideanSpace ℝ (Fin 2))) ∈
            closure ((↑) '' C : Set (OnePoint (EuclideanSpace ℝ (Fin 2)))) :=
          himg_cl ⟨q, hCadj, rfl⟩
        exact closure_mono hCface this
      have hq_not :
          (q : OnePoint (EuclideanSpace ℝ (Fin 2))) ∉ D.toDrawing.onePoint.faceSet F :=
        (D.toDrawing.onePoint.faceSet_disjoint_support F).notMem_of_mem_right hq_one
      have hFopen := D.toDrawing.onePoint.faceSet_isOpen hclsupp F
      change _ ∈ frontier (D.toDrawing.onePoint.faceSet F)
      rw [hFopen.frontier_eq]
      exact ⟨hq_cl, hq_not⟩
  exact hsec_eq.trans hfaces_p.symm

/-- The sides of an open cell are locally constant along the cell. -/
theorem facesAt_eq [G.Finite] (D : PLDrawing G (EuclideanSpace ℝ (Fin 2))) {e : E(G)}
    {p q : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ pathInterior (D.toDrawing.edgePath e))
    (hq : q ∈ pathInterior (D.toDrawing.edgePath e)) :
    D.facesAt p = D.facesAt q := by
  classical
  let PI := pathInterior (D.toDrawing.edgePath e)
  have hPIc : IsConnected PI := by
    simpa only [PI, pathInterior] using
      (isConnected_Ioo (show (0 : unitInterval) < 1 from zero_lt_one)).image _
        (D.toDrawing.edgePath e).continuous.continuousOn
  have hloc (x : EuclideanSpace ℝ (Fin 2)) (hx : x ∈ PI) :
      ∃ ε > 0, ∀ y ∈ PI, dist x y < ε → D.facesAt y = D.facesAt x := by
    obtain ⟨ρ, hρ, Y, hYsph, hYcard, _, hstar⟩ := D.exists_radius_edgeInterior hx
    refine ⟨ρ, hρ, ?_⟩
    intro y hy hydist
    exact facesAt_eq_of_mem_star_ball D hx hy hρ hYsph hYcard hstar
      (mem_ball.mpr (by rwa [PseudoMetricSpace.dist_comm]))
  let f : PI → Set D.toDrawing.onePoint.Face := fun z => D.facesAt z.1
  have hf_loc : ∀ z : PI, ∃ U : Set PI, IsOpen U ∧ z ∈ U ∧ ∀ z' ∈ U, f z' = f z := by
    intro z
    obtain ⟨ε, hε, H⟩ := hloc z.1 z.2
    refine ⟨Subtype.val ⁻¹' ball (z : EuclideanSpace ℝ (Fin 2)) ε,
      isOpen_ball.preimage continuous_subtype_val, mem_ball_self hε, ?_⟩
    intro z' hz'
    have hzball : (z'.1 : EuclideanSpace ℝ (Fin 2)) ∈ ball z.1 ε := hz'
    exact H z'.1 z'.2 (by
      simpa [PseudoMetricSpace.dist_comm] using (mem_ball.mp hzball))
  let U : Set PI := {z | f z = f ⟨p, hp⟩}
  have hUopen : IsOpen U := by
    rw [isOpen_iff_forall_mem_open]
    intro z hz
    obtain ⟨V, hVopen, hzV, hV⟩ := hf_loc z
    refine ⟨V, fun z' hz' ↦ ?_, hVopen, hzV⟩
    change f z' = f ⟨p, hp⟩
    rw [hV z' hz', hz]
  have hUclosed : IsClosed U := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro z hz
    obtain ⟨V, hVopen, hzV, hV⟩ := hf_loc z
    refine ⟨V, fun z' hz' hz'U ↦ hz ?_, hVopen, hzV⟩
    change f z = f ⟨p, hp⟩
    rw [← hV z' hz']
    exact hz'U
  have hUne : U.Nonempty := ⟨⟨p, hp⟩, rfl⟩
  have hUuniv : U = univ := by
    have : ConnectedSpace PI := isConnected_iff_connectedSpace.mp hPIc
    exact IsClopen.eq_univ ⟨hUclosed, hUopen⟩ hUne
  have hqU : (⟨q, hq⟩ : PI) ∈ U := by
    rw [hUuniv]; trivial
  exact hqU.symm

end PLDrawing

end

end Graph
