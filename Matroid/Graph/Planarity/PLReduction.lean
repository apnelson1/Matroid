import Matroid.Graph.Planarity.PLDrawing
import Matroid.ForMathlib.Geometry.PolygonalPath.Radial
import Matroid.ForMathlib.Analysis.Convex.RadialPoint
import Mathlib.Topology.Subpath

/-!
# Every drawing can be replaced by a polygonal one

Status.md §2.6: a finite loopless graph drawn in a real normed space can be drawn with polygonal
edges, keeping the vertex positions. With `PLPlanar.planar` this gives `Planar ↔ PLPlanar`,
after which every topological argument in the Kuratowski development runs in the polygonal category,
where the local structure of a drawing is elementary. It is what removes Jordan–Schoenflies and
Janiszewski from the project's assumptions.

The theorem does *not* say that the given drawing is ambiently equivalent to a polygonal one — that
is the Schoenflies statement, which is neither proved nor needed. It produces *some* polygonal
drawing of the same abstract graph, with the same vertex positions.

Nothing here is special to the plane, so the statements are over a real normed space; `Planar` is
the case `V := EuclideanSpace ℝ (Fin 2)`. Looplessness is a hypothesis of the argument rather than
of the truth of the statement: the balls at the two ends of an edge are assumed disjoint throughout.
Loops are Status.md §12.

## The shape of the argument

Status.md's six steps become four statements. Only the first two mention a graph, and only those
two are in this file:

1. `Drawing.exists_vertexRadius` — a positive radius at each vertex, with the closed balls pairwise
   disjoint and each ball meeting the drawing only in the vertex and the cells at that vertex.
2. `Drawing.exists_middlePaths` — the *middle* of each cell: the part between its last exit from
   the ball at one end and its first entry into the ball at the other. Middles are pairwise
   disjoint, avoid the balls at all other vertices, and end on the two spheres.
3. `exists_polygonalPath_family_of_disjoint` — the analytic step: finitely many pairwise disjoint
   compact paths, each avoiding a closed set of its own, can be replaced by polygonal paths with
   the same endpoints and the same disjointness.
4. `exists_isSimple_radial` — the geometric step: a polygonal path between two disjoint balls can be
   re-cut at its last exit and first entry and joined to the two centres by radii, giving an
   *embedded* polygonal arc that meets each ball in exactly one radius.

Steps 3 and 4 mention no graph, and live in
`Matroid/ForMathlib/Geometry/PolygonalPath/Radial.lean` (Kuratowski `Decisions.md` D14). Step 4 is
where Status.md's ordering matters: the radii are chosen using the polyline's last exit, not the
original arc's.

What remains here is the bookkeeping the graph supplies — which balls, which cells, which edges —
and `Drawing.exists_plDrawing`, which assembles the result and discharges the disjointness
obligations `PLDrawing.ofCells` demands.

## Main statements

* `Graph.Drawing.exists_plDrawing` : the reduction, over a real normed space.
* `Graph.Planar.plPlanar` and `Graph.planar_iff_plPlanar` : Status.md 2.6 and 2.7.
-/

open Function Set Topology Metric PolygonalPath
open scoped unitInterval

namespace Graph

noncomputable section

universe u

variable {α β : Type*} {G H : Graph α β} {V : Type u} [NormedAddCommGroup V]

/-! ### Step 1: separating the vertices -/

/-- A vertex image does not lie on the cell of a non-incident edge. -/
lemma Drawing.vertex_notMem_range_edgePath_of_not_inc (D : Drawing G V) {x : V(G)} {e : E(G)}
    (h : ¬ G.Inc e.1 x.1) : D.vertex x ∉ range (D.edgePath e) := by
  rintro ⟨t, ht⟩
  have hends : x = edgeSource e ∨ x = edgeTarget e → G.Inc e.1 x.1 := by
    rintro (rfl | rfl)
    · exact (isLink_edgeSource_edgeTarget e).inc_left
    exact (isLink_edgeSource_edgeTarget e).inc_right
  obtain rfl | rfl | htI := unitInterval.eq_zero_or_eq_one_or_mem_Ioo t
  · grind [D.vertex_injective]
  · grind [D.vertex_injective]
  exact (D.pathInterior_edgePath_disjoint_vertex e).notMem_of_mem_left ⟨t, htI, ht⟩ ⟨x, rfl⟩

/-- A radius at each vertex whose closed balls are pairwise disjoint and meet the drawing only in
that vertex and the cells at it.

Status.md's Step 1 states the last inclusion without the `{D.vertex x}` summand, which fails for an
isolated vertex, where the union on the right is empty. -/
theorem Drawing.exists_vertexRadius [G.Finite] (D : Drawing G V) : ∃ r : V(G) → ℝ, (∀ x, 0 < r x) ∧
    (Pairwise fun x y ↦ Disjoint (closedBall (D.vertex x) (r x)) (closedBall (D.vertex y) (r y))) ∧
    ∀ x, closedBall (D.vertex x) (r x) ∩ D.support ⊆ {D.vertex x} ∪
    ⋃ e ∈ {e : E(G) | G.Inc e.1 x.1}, range (D.edgePath e) := by
  classical
  -- `Graph.dist` / `Graph.dist_comm` shadow the metric versions in this namespace.
  have mdist_pos {a b : V} : 0 < dist a b ↔ a ≠ b := @dist_pos V _ a b
  have one_third_lt_one : (1 / 3 : ℝ) < 1 := by norm_num
  have : Fintype V(G) := Fintype.ofFinite _
  have : Fintype E(G) := Fintype.ofFinite _
  -- Status.md: empty minima default to `1`, encoded by adjoining `1` to each distance set.
  let vertDists (x : V(G)) : Finset ℝ :=
    (Finset.univ.erase x).image fun y ↦ dist (D.vertex x) (D.vertex y)
  let edgeDists (x : V(G)) : Finset ℝ :=
    ((Finset.univ.filter fun e : E(G) ↦ ¬ G.Inc e.1 x.1).image fun e ↦
      infDist (D.vertex x) (range (D.edgePath e)))
  let r (x : V(G)) : ℝ :=
    (1 / 3) * ((insert (1 : ℝ) (vertDists x ∪ edgeDists x)).min' (Finset.insert_nonempty ..))
  have hrange_nonempty (e : E(G)) : (range (D.edgePath e)).Nonempty := ⟨_, ⟨0, rfl⟩⟩
  have hrange_closed (e : E(G)) : IsClosed (range (D.edgePath e)) :=
    (isCompact_range (D.edgePath e).continuous).isClosed
  have hpos (x : V(G)) : 0 < r x := by
    refine mul_pos (by norm_num) ?_
    rw [Finset.lt_min'_iff]
    intro d hd
    rw [Finset.mem_insert, Finset.mem_union] at hd
    obtain rfl | hV | hE := hd
    · exact one_pos
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hV
      exact mdist_pos.mpr (D.vertex_injective.ne (Finset.mem_erase.mp hy).1.symm)
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hE
    exact (hrange_closed e).notMem_iff_infDist_pos (hrange_nonempty e) |>.mp
      (D.vertex_notMem_range_edgePath_of_not_inc (Finset.mem_filter.mp he).2)
  have hle_vert (x y : V(G)) (hyx : y ≠ x) : r x ≤ (1 / 3) * dist (D.vertex x) (D.vertex y) := by
    refine mul_le_mul_of_nonneg_left (Finset.min'_le _ _ ?_) (by norm_num)
    exact Finset.mem_insert_of_mem <| Finset.mem_union_left _ <| Finset.mem_image.mpr
      ⟨y, Finset.mem_erase.mpr ⟨hyx, Finset.mem_univ _⟩, rfl⟩
  have hle_edge (x : V(G)) (e : E(G)) (he : ¬ G.Inc e.1 x.1) :
      r x ≤ (1 / 3) * infDist (D.vertex x) (range (D.edgePath e)) := by
    refine mul_le_mul_of_nonneg_left (Finset.min'_le _ _ ?_) (by norm_num)
    exact Finset.mem_insert_of_mem <| Finset.mem_union_right _ <| Finset.mem_image.mpr
      ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, rfl⟩
  refine ⟨r, hpos, fun x y hxy ↦ closedBall_disjoint_closedBall ?_, ?_⟩
  · have hd : 0 < dist (D.vertex x) (D.vertex y) := mdist_pos.mpr (D.vertex_injective.ne hxy)
    refine lt_of_le_of_lt (b := (2 / 3) * _)
      ((add_le_add (hle_vert x y hxy.symm) (hle_vert y x hxy)).trans ?_)
      <| (mul_lt_iff_lt_one_left hd).mpr (by norm_num)
    rw [dist_comm (D.vertex y) (D.vertex x), ← two_mul, ← mul_assoc]
    norm_num
  rintro x z ⟨hzball, hzsupp⟩
  rw [mem_closedBall, dist_comm] at hzball
  rw [D.support_eq, mem_union, mem_iUnion] at hzsupp
  obtain ⟨y, rfl⟩ | ⟨e, he⟩ := hzsupp
  · suffices y = x by simp [this]
    by_contra! hyx
    exact hzball.not_gt <| (hle_vert x y hyx).trans_lt <| mul_lt_iff_lt_one_left
      (mdist_pos.mpr (D.vertex_injective.ne hyx.symm)) |>.mpr one_third_lt_one
  obtain hinc | hinc := em (G.Inc e.1 x.1)
  · exact Or.inr <| mem_biUnion hinc he
  exact ((infDist_le_dist_of_mem he).trans hzball |>.not_gt <| (hle_edge x e hinc).trans_lt
    <| (mul_lt_iff_lt_one_left <| (hrange_closed e).notMem_iff_infDist_pos (hrange_nonempty e)
    |>.mp (D.vertex_notMem_range_edgePath_of_not_inc hinc)).mpr one_third_lt_one).elim

/-! ### Step 2: the middle of each cell -/

/-- The middles of the cells: for each edge, the part of its cell running from its last exit from
the ball at one end to its first entry into the ball at the other. Distinct middles are disjoint,
each avoids the balls at all vertices other than its own two ends, and each meets those two balls in
exactly its two endpoints, which lie on the spheres.

Stated as a family rather than one edge at a time because the disjointness across edges is what the
next step consumes. The middle is presented as a path rather than as a set so that it can be fed to
the approximation lemma. -/
theorem Drawing.exists_middlePaths [G.Finite] [G.Loopless] (D : Drawing G V) {r : V(G) → ℝ}
    (hpos : ∀ x, 0 < r x) (hdisj : Pairwise fun x y ↦ Disjoint (closedBall (D.vertex x) (r x))
      (closedBall (D.vertex y) (r y))) (hball : ∀ x, closedBall (D.vertex x) (r x) ∩ D.support ⊆
      {D.vertex x} ∪ ⋃ e ∈ {e : E(G) | G.Inc e.1 x.1}, range (D.edgePath e)) :
    ∃ (a b : E(G) → V) (Q : ∀ e, Path (a e) (b e)), (∀ e, range (Q e) ⊆ range (D.edgePath e)) ∧
      (∀ e, dist (a e) (D.vertex (edgeSource e)) = r (edgeSource e)) ∧
      (∀ e, dist (b e) (D.vertex (edgeTarget e)) = r (edgeTarget e)) ∧
      (∀ e, range (Q e) ∩ closedBall (D.vertex (edgeSource e)) (r (edgeSource e)) = {a e}) ∧
      (∀ e, range (Q e) ∩ closedBall (D.vertex (edgeTarget e)) (r (edgeTarget e)) = {b e}) ∧
      (∀ e, ∀ x, x ≠ edgeSource e → x ≠ edgeTarget e →
        Disjoint (range (Q e)) (closedBall (D.vertex x) (r x))) ∧
      Pairwise fun e f ↦ Disjoint (range (Q e)) (range (Q f)) := by
  have hsrc_ne_tgt (e : E(G)) : edgeSource e ≠ edgeTarget e := by
    exact fun heq ↦ (isLink_edgeSource_edgeTarget e).ne (congrArg Subtype.val heq)
  have hinc_ends (e : E(G)) {x : V(G)} (hx : G.Inc e.1 x.1) :
      x = edgeSource e ∨ x = edgeTarget e := hx.eq_or_eq_of_isLink (isLink_edgeSource_edgeTarget e)
        |>.imp (fun h ↦ Subtype.ext h) (fun h ↦ Subtype.ext h)
  choose t_e s_e ht_lt hdist_a hdist_b hinter_a hinter_b using fun e : E(G) ↦
    (D.edgePath e).exists_lastExit_firstEntry (hdisj (hsrc_ne_tgt e))
      (mem_closedBall_self (hpos _).le) (mem_closedBall_self (hpos _).le)
  let a : E(G) → V := fun e ↦ D.edgePath e (t_e e)
  let b : E(G) → V := fun e ↦ D.edgePath e (s_e e)
  let Q : ∀ e, Path (a e) (b e) := fun e ↦ (D.edgePath e).subpath (t_e e) (s_e e)
  have hQ_range (e : E(G)) : range (Q e) = D.edgePath e '' Icc (t_e e) (s_e e) :=
    Path.range_subpath_of_le _ _ _ (ht_lt e).le
  have hQ_subset (e : E(G)) : range (Q e) ⊆ range (D.edgePath e) :=
    hQ_range .. ▸ image_subset_range ..
  have hmeet_a (e : E(G)) :
      range (Q e) ∩ closedBall (D.vertex (edgeSource e)) (r (edgeSource e)) = {a e} := by
    rw [hQ_range, show a e = D.edgePath e (t_e e) from rfl]
    exact hinter_a e
  have hmeet_b (e : E(G)) :
      range (Q e) ∩ closedBall (D.vertex (edgeTarget e)) (r (edgeTarget e)) = {b e} := by
    rw [hQ_range, show b e = D.edgePath e (s_e e) from rfl]
    exact hinter_b e
  refine ⟨a, b, Q, hQ_subset, hdist_a, hdist_b, hmeet_a, hmeet_b, fun e x hxu hxv ↦
    disjoint_left.mpr fun z hzQ hzB ↦ ?_, fun e f hef ↦ disjoint_left.mpr fun z hze hzf ↦ ?_⟩
  · have hzmem := hball x ⟨hzB, (D.edgePath_range_subset_support e (hQ_subset e hzQ))⟩
    rw [mem_union, mem_singleton_iff] at hzmem
    obtain rfl | hzE := hzmem
    · exact D.vertex_notMem_range_edgePath_of_not_inc
        (fun hinc ↦ (hinc_ends e hinc).elim hxu hxv) (hQ_subset e hzQ)
    obtain ⟨f, hf, hzf⟩ := mem_iUnion₂.mp hzE
    obtain rfl | hef := eq_or_ne f e
    · grind
    have hz_end : z = D.vertex (edgeSource e) ∨ z = D.vertex (edgeTarget e) := by
      simpa [mem_inter_iff, mem_insert_iff, mem_singleton_iff] using
        ((D.range_edgePath_inter hef.symm).subset ⟨hQ_subset e hzQ, hzf⟩).1
    obtain rfl | rfl := hz_end
    · exact (hdisj hxu.symm).notMem_of_mem_left (mem_closedBall_self (hpos _).le) hzB
    exact (hdisj hxv.symm).notMem_of_mem_left (mem_closedBall_self (hpos _).le) hzB
  have ha_ne : a e ≠ D.vertex (edgeSource e) := by
    intro h
    have : dist (a e) (D.vertex (edgeSource e)) = 0 := by simp [h]
    exact (hpos _).ne' (hdist_a e ▸ this)
  have hb_ne : b e ≠ D.vertex (edgeTarget e) := by
    intro h
    have : dist (b e) (D.vertex (edgeTarget e)) = 0 := by simp [h]
    exact (hpos _).ne' (hdist_b e ▸ this)
  obtain hz | hz : z = D.vertex (edgeSource e) ∨ z = D.vertex (edgeTarget e) := by
    simpa [mem_inter_iff, mem_insert_iff, mem_singleton_iff] using
      ((D.range_edgePath_inter hef).subset ⟨hQ_subset e hze, hQ_subset f hzf⟩).1
  · have : z ∈ range (Q e) ∩ closedBall (D.vertex (edgeSource e)) (r (edgeSource e)) :=
      ⟨hze, by rw [hz]; exact mem_closedBall_self ((hpos _).le)⟩
    rw [hmeet_a, mem_singleton_iff, hz] at this
    exact ha_ne this.symm
  have : z ∈ range (Q e) ∩ closedBall (D.vertex (edgeTarget e)) (r (edgeTarget e)) :=
    ⟨hze, by rw [hz]; exact mem_closedBall_self ((hpos _).le)⟩
  rw [hmeet_b, mem_singleton_iff, hz] at this
  exact hb_ne this.symm

/-! ### The reduction -/


/-- Status.md 2.6: a drawing of a finite loopless graph in a real normed space can be replaced by a
polygonal drawing with the same vertex positions. -/
theorem Drawing.exists_plDrawing [G.Finite] [G.Loopless] [NormedSpace ℝ V] (D : Drawing G V) :
    ∃ Q : PLDrawing G V, ∀ x, Q.vertex x = D.vertex x := by
  obtain ⟨r, hpos, hdisj, hball⟩ := D.exists_vertexRadius
  obtain ⟨a, b, Mid, _hMid_sub, hdist_a, hdist_b, _hmeet_a, _hmeet_b, havoid, hMid_disj⟩ :=
    D.exists_middlePaths hpos hdisj hball
  have hsrc_ne_tgt (e : E(G)) : edgeSource e ≠ edgeTarget e :=
    fun heq ↦ (isLink_edgeSource_edgeTarget e).ne (congrArg Subtype.val heq)
  -- Closed obstacle sets: balls at vertices that are not ends of `e`.
  let K : E(G) → Set V := fun e ↦
    ⋃ x ∈ {x : V(G) | x ≠ edgeSource e ∧ x ≠ edgeTarget e}, closedBall (D.vertex x) (r x)
  have hK_closed (e : E(G)) : IsClosed (K e) :=
    (toFinite _).isClosed_biUnion fun _ _ ↦ isClosed_closedBall
  have hMid_K (e : E(G)) : Disjoint (range (Mid e)) (K e) := by
    refine disjoint_left.mpr fun z hzMid hzK ↦ ?_
    obtain ⟨x, hx, hzB⟩ := mem_iUnion₂.mp hzK
    exact (havoid e x hx.1 hx.2).notMem_of_mem_left hzMid hzB
  obtain ⟨Ppoly, hP_disj, hP_K⟩ :=
    exists_polygonalPath_family_of_disjoint Mid hMid_disj K hK_closed hMid_K
  choose zu zv cell hcell using fun e : E(G) ↦ exists_isSimple_radial (hpos _) (hpos _)
    (hdisj (hsrc_ne_tgt e)) (Ppoly e) (mem_closedBall.mpr (hdist_a e).le)
    (mem_closedBall.mpr (hdist_b e).le)
  have hzu_dist (e : E(G)) :
      dist (zu e) (D.vertex (edgeSource e)) = r (edgeSource e) := (hcell e).2.1
  have hzv_dist (e : E(G)) :
      dist (zv e) (D.vertex (edgeTarget e)) = r (edgeTarget e) := (hcell e).2.2.1
  have hcell_src (e : E(G)) : (cell e).toSet ∩ closedBall (D.vertex (edgeSource e))
      (r (edgeSource e)) = segment ℝ (D.vertex (edgeSource e)) (zu e) := (hcell e).2.2.2.1
  have hcell_tgt (e : E(G)) : (cell e).toSet ∩ closedBall (D.vertex (edgeTarget e))
      (r (edgeTarget e)) = segment ℝ (D.vertex (edgeTarget e)) (zv e) := (hcell e).2.2.2.2.1
  have hcell_mid (e : E(G)) : (cell e).toSet \ (ball (D.vertex (edgeSource e)) (r (edgeSource e)) ∪
      ball (D.vertex (edgeTarget e)) (r (edgeTarget e))) ⊆ (Ppoly e).toSet := (hcell e).2.2.2.2.2
  have hzu_mem_P (e : E(G)) : zu e ∈ (Ppoly e).toSet := by
    refine hcell_mid e ⟨(hcell_src .. ▸ right_mem_segment ℝ ..).1, ?_⟩
    rintro (hu | hv)
    · exact (lt_self_iff_false _).mp <| (mem_ball.mp hu).trans_eq (hzu_dist e).symm
    exact (hdisj (hsrc_ne_tgt e)).notMem_of_mem_left (mem_closedBall.mpr (hzu_dist e).le)
      (mem_closedBall.mpr (mem_ball.mp hv).le)
  have hzv_mem_P (e : E(G)) : zv e ∈ (Ppoly e).toSet := by
    refine hcell_mid e ⟨(hcell_tgt .. ▸ right_mem_segment ..).1, ?_⟩
    rintro (hu | hv)
    · exact (hdisj (hsrc_ne_tgt e)).notMem_of_mem_left (mem_closedBall.mpr (mem_ball.mp hu).le)
        (mem_closedBall.mpr (hzv_dist e).le)
    exact (lt_self_iff_false _).mp <| (mem_ball.mp hv).trans_eq (hzv_dist e).symm
  have hcell_avoid (e : E(G)) (x : V(G)) (hxu : x ≠ edgeSource e) (hxv : x ≠ edgeTarget e) :
      Disjoint (cell e).toSet (closedBall (D.vertex x) (r x)) := by
    refine disjoint_left.mpr fun w hwcell hwB ↦ ?_
    obtain hwu | hwu := em (w ∈ closedBall (D.vertex (edgeSource e)) (r (edgeSource e)))
    · exact (hdisj hxu.symm).notMem_of_mem_left hwu hwB
    obtain hwv | hwv := em (w ∈ closedBall (D.vertex (edgeTarget e)) (r (edgeTarget e)))
    · exact (hdisj hxv.symm).notMem_of_mem_left hwv hwB
    have hwP : w ∈ (Ppoly e).toSet := hcell_mid e ⟨hwcell, by
        rintro (hu | hv)
        · exact hwu (mem_closedBall.mpr (mem_ball.mp hu).le)
        exact hwv (mem_closedBall.mpr (mem_ball.mp hv).le)⟩
    exact (hP_K e).notMem_of_mem_left hwP <| mem_iUnion₂.mpr ⟨x, ⟨hxu, hxv⟩, hwB⟩
  have hlen (e : E(G)) : 0 < (cell e).length :=
    length_pos_of_ne (cell e) (D.vertex_injective.ne (hsrc_ne_tgt e))
  have hsimple (e : E(G)) : (cell e).IsSimpleArcOrLoop := (hcell e).1.isSimpleArcOrLoop (hlen e)
  have hcv (e : E(G)) : Disjoint ((cell e).toSet \
      {D.vertex (edgeSource e), D.vertex (edgeTarget e)}) (range D.vertex) := by
    refine disjoint_left.mpr ?_
    rintro w ⟨hwcell, hwne⟩ ⟨x, rfl⟩
    have hxne : x ≠ edgeSource e ∧ x ≠ edgeTarget e := by
      constructor
      · intro h; exact hwne (by simp [h])
      · intro h; exact hwne (by simp [h])
    exact (hcell_avoid e x hxne.1 hxne.2).notMem_of_mem_left hwcell <|
      mem_closedBall_self (hpos x).le
  -- The two ends of an edge carry the same three facts. Quantifying over *ends* rather than
  -- naming `edgeSource` and `edgeTarget` separately is what keeps `hcc` below from splitting
  -- into the four cases (end of `e`) × (end of `f`), each with the same body.
  have hend (g : E(G)) (x : V(G)) (hx : x = edgeSource g ∨ x = edgeTarget g) :
      ∃ z, dist z (D.vertex x) = r x ∧ (cell g).toSet ∩ closedBall (D.vertex x) (r x) =
      segment ℝ (D.vertex x) z ∧ z ∈ (Ppoly g).toSet := by
    obtain rfl | rfl := hx
    · exact ⟨zu g, hzu_dist g, hcell_src g, hzu_mem_P g⟩
    exact ⟨zv g, hzv_dist g, hcell_tgt g, hzv_mem_P g⟩
  -- Inside the ball at an end `x` of `e`, the cell of `e` is the radius to its sphere point. A
  -- point also on the cell of `f` is on a second radius of the same ball, and the two radii have
  -- distinct sphere points because the middles `Ppoly` are disjoint; so it is the centre.
  have key (e f : E(G)) (hef : e ≠ f) (x : V(G)) (hx : x = edgeSource e ∨ x = edgeTarget e)
      {w : V} (hwe : w ∈ (cell e).toSet) (hwf : w ∈ (cell f).toSet)
      (hwB : w ∈ closedBall (D.vertex x) (r x)) : w = D.vertex x := by
    obtain ⟨ze, hze_dist, hze_cell, hze_P⟩ := hend e x hx
    have hwseg : w ∈ segment ℝ (D.vertex x) ze := hze_cell ▸ ⟨hwe, hwB⟩
    by_cases hxf : x = edgeSource f ∨ x = edgeTarget f
    · obtain ⟨zf, hzf_dist, hzf_cell, hzf_P⟩ := hend f x hxf
      have hzne : ze ≠ zf := fun hz ↦
        (hP_disj hef).notMem_of_mem_left hze_P (hz ▸ hzf_P)
      have hwsegf : w ∈ segment ℝ (D.vertex x) zf := hzf_cell ▸ ⟨hwf, hwB⟩
      have hne₁ : ze ≠ D.vertex x := dist_pos.mp (by rw [hze_dist]; exact hpos x)
      exact eq_center_of_mem_two_radii hne₁ (hzf_dist.trans hze_dist.symm) hzne hwseg hwsegf
    push Not at hxf
    exact ((hcell_avoid f x hxf.1 hxf.2).notMem_of_mem_left hwf hwB).elim
  have hcc (e f : E(G)) (hef : e ≠ f) : Disjoint
      ((cell e).toSet \ {D.vertex (edgeSource e), D.vertex (edgeTarget e)})
      ((cell f).toSet \ {D.vertex (edgeSource f), D.vertex (edgeTarget f)}) := by
    refine disjoint_left.mpr fun w ⟨hwe, hwe_ne⟩ ⟨hwf, _hwf_ne⟩ ↦ ?_
    obtain hwe_u | hwe_u := em (w ∈ closedBall (D.vertex (edgeSource e)) (r (edgeSource e)))
    · exact hwe_ne (by simp [key e f hef _ (Or.inl rfl) hwe hwf hwe_u])
    obtain hwe_v | hwe_v := em (w ∈ closedBall (D.vertex (edgeTarget e)) (r (edgeTarget e)))
    · exact hwe_ne (by simp [key e f hef _ (Or.inr rfl) hwe hwf hwe_v])
    have hwP : w ∈ (Ppoly e).toSet :=
      hcell_mid e ⟨hwe, by
        rintro (hu | hv)
        · exact hwe_u (mem_closedBall.mpr ((mem_ball.mp hu).le))
        exact hwe_v (mem_closedBall.mpr (le_of_lt (mem_ball.mp hv)))⟩
    -- `w` is outside both balls at `e`, so *any* ball containing it is an obstacle in `K e`.
    have hfar (y : V(G)) (hy : w ∈ closedBall (D.vertex y) (r y)) : False := by
      by_cases hye : y = edgeSource e ∨ y = edgeTarget e
      · grind
      push Not at hye
      exact (hP_K e).notMem_of_mem_left hwP (mem_iUnion₂.mpr ⟨y, ⟨hye.1, hye.2⟩, hy⟩)
    obtain hwf_u | hwf_u := em (w ∈ closedBall (D.vertex (edgeSource f)) (r (edgeSource f)))
    · exact hfar _ hwf_u
    obtain hwf_v | hwf_v := em (w ∈ closedBall (D.vertex (edgeTarget f)) (r (edgeTarget f)))
    · exact hfar _ hwf_v
    have hwPf : w ∈ (Ppoly f).toSet :=
      hcell_mid f ⟨hwf, by
        rintro (hu | hv)
        · exact hwf_u (mem_closedBall.mpr ((mem_ball.mp hu).le))
        exact hwf_v (mem_closedBall.mpr (le_of_lt (mem_ball.mp hv)))⟩
    exact (hP_disj hef).notMem_of_mem_left hwP hwPf
  refine ⟨PLDrawing.ofCells D.vertex D.vertex_injective cell hsimple hcv hcc, fun x ↦ ?_⟩
  exact PLDrawing.ofCells_vertex x

/-- Status.md 2.6 in the plane. -/
theorem Planar.plPlanar [G.Finite] [G.Loopless] (hG : G.Planar) : G.PLPlanar :=
  ⟨hG.some.exists_plDrawing.choose⟩

/-- Status.md 2.7. -/
theorem planar_iff_plPlanar [G.Finite] [G.Loopless] : G.Planar ↔ G.PLPlanar :=
  ⟨Planar.plPlanar, PLPlanar.planar⟩

end

end Graph
