import Matroid.Graph.Planarity.PLDrawing
import Matroid.ForMathlib.Geometry.PolygonalPath.Approximation
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

Status.md's six steps become four statements. Given a drawing `D`:

1. `Drawing.exists_vertexRadius` — a positive radius at each vertex, with the closed balls pairwise
   disjoint and each ball meeting the drawing only in the vertex and the cells at that vertex.
2. `Drawing.exists_middlePaths` — the *middle* of each cell: the part between its last exit from
   the ball at one end and its first entry into the ball at the other. Middles are pairwise
   disjoint, avoid the balls at all other vertices, and end on the two spheres.
3. `exists_polygonalPath_family_of_disjoint` — the analytic step, stated without reference to a
   graph: finitely many pairwise disjoint compact paths, each avoiding a closed set of its own, can
   be replaced by polygonal paths with the same endpoints and the same disjointness. This is the
   only place approximation is used, and the only reason this file imports it.
4. `exists_isSimple_radial` — the geometric step: a polygonal path between two disjoint balls can be
   re-cut at its last exit and first entry and joined to the two centres by radii, giving an
   *embedded* polygonal arc that meets each ball in exactly one radius.

Step 4 is where Status.md's ordering matters: the radii are chosen using the polyline's last exit,
not the original arc's. Two radii of the same ball ending at distinct points of its sphere meet only
at the centre — true in any normed space, since a point of `[x, y]` with `‖y - x‖ = ρ` is determined
by its distance to `x`.

## Main statements

* `Graph.Drawing.exists_plDrawing` : the reduction, over a real normed space.
* `Graph.Planar.plPlanar` and `Graph.planar_iff_plPlanar` : Status.md 2.6 and 2.7.
-/

open Function Set Topology Metric
open scoped unitInterval

namespace Graph

noncomputable section

universe u

variable {α β : Type*} {G H : Graph α β}
variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-! ### Step 1: separating the vertices -/

set_option linter.unusedSectionVars false in
/-- A vertex image does not lie on the cell of a non-incident edge. -/
lemma Drawing.vertex_notMem_range_edgePath_of_not_inc (D : Drawing G V)
    {x : V(G)} {e : E(G)} (h : ¬ G.Inc e.1 x.1) : D.vertex x ∉ range (D.edgePath e) := by
  rintro ⟨t, ht⟩
  have hends : x = edgeSource e ∨ x = edgeTarget e → G.Inc e.1 x.1 := by
    rintro (rfl | rfl)
    · exact (isLink_edgeSource_edgeTarget e).inc_left
    · exact (isLink_edgeSource_edgeTarget e).inc_right
  have ht01 : (t : ℝ) = 0 ∨ (t : ℝ) = 1 ∨ t ∈ Ioo (0 : I) 1 := by
    have ht0 : 0 ≤ (t : ℝ) := t.2.1
    have ht1 : (t : ℝ) ≤ 1 := t.2.2
    rcases eq_or_lt_of_le ht0 with ht0' | ht0'
    · exact Or.inl ht0'.symm
    · rcases eq_or_lt_of_le ht1 with ht1' | ht1'
      · exact Or.inr (Or.inl ht1')
      · exact Or.inr (Or.inr ⟨ht0', ht1'⟩)
  rcases ht01 with ht0 | ht1 | htI
  · apply h
    refine hends <| Or.inl <| D.vertex_injective ?_
    rw [show t = 0 from Subtype.ext ht0, Path.source] at ht
    exact ht.symm
  · apply h
    refine hends <| Or.inr <| D.vertex_injective ?_
    rw [show t = 1 from Subtype.ext ht1, Path.target] at ht
    exact ht.symm
  · exact (D.pathInterior_edgePath_disjoint_vertex e).notMem_of_mem_left ⟨t, htI, ht⟩
      ⟨x, rfl⟩

/-- A radius at each vertex whose closed balls are pairwise disjoint and meet the drawing only in
that vertex and the cells at it.

Status.md's Step 1 states the last inclusion without the `{D.vertex x}` summand, which fails for an
isolated vertex, where the union on the right is empty. -/
theorem Drawing.exists_vertexRadius [G.Finite] (D : Drawing G V) :
    ∃ r : V(G) → ℝ, (∀ x, 0 < r x) ∧
      (Pairwise fun x y ↦ Disjoint (closedBall (D.vertex x) (r x))
        (closedBall (D.vertex y) (r y))) ∧
      ∀ x, closedBall (D.vertex x) (r x) ∩ D.support ⊆
        {D.vertex x} ∪ ⋃ e ∈ {e : E(G) | G.Inc e.1 x.1}, range (D.edgePath e) := by
  classical
  -- `Graph.dist` / `Graph.dist_comm` shadow the metric versions in this namespace.
  have mdist_pos {a b : V} : 0 < Dist.dist a b ↔ a ≠ b := @dist_pos V _ a b
  have mdist_comm (a b : V) : Dist.dist a b = Dist.dist b a :=
    PseudoMetricSpace.dist_comm a b
  have one_third_lt_one : (1 / 3 : ℝ) < 1 := by norm_num
  have two_thirds_lt_one : (2 / 3 : ℝ) < 1 := by norm_num
  have : Fintype V(G) := Fintype.ofFinite _
  have : Fintype E(G) := Fintype.ofFinite _
  -- Status.md: empty minima default to `1`, encoded by adjoining `1` to each finite set of distances.
  let vertDists (x : V(G)) : Finset ℝ :=
    (Finset.univ.erase x).image fun y ↦ Dist.dist (D.vertex x) (D.vertex y)
  let edgeDists (x : V(G)) : Finset ℝ :=
    ((Finset.univ.filter fun e : E(G) ↦ ¬ G.Inc e.1 x.1).image fun e ↦
      infDist (D.vertex x) (range (D.edgePath e)))
  let r (x : V(G)) : ℝ :=
    (1 / 3) * ((insert (1 : ℝ) (vertDists x ∪ edgeDists x)).min'
      (Finset.insert_nonempty _ _))
  have hrange_nonempty (e : E(G)) : (range (D.edgePath e)).Nonempty := ⟨_, ⟨0, rfl⟩⟩
  have hrange_closed (e : E(G)) : IsClosed (range (D.edgePath e)) :=
    (isCompact_range (D.edgePath e).continuous).isClosed
  have hpos (x : V(G)) : 0 < r x := by
    refine mul_pos (by norm_num) ?_
    rw [Finset.lt_min'_iff]
    intro d hd
    rw [Finset.mem_insert, Finset.mem_union] at hd
    rcases hd with rfl | hV | hE
    · exact one_pos
    · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hV
      exact mdist_pos.mpr (D.vertex_injective.ne (Finset.mem_erase.mp hy).1.symm)
    · obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hE
      exact (hrange_closed e).notMem_iff_infDist_pos (hrange_nonempty e) |>.mp
        (D.vertex_notMem_range_edgePath_of_not_inc (Finset.mem_filter.mp he).2)
  have hle_vert (x y : V(G)) (hyx : y ≠ x) :
      r x ≤ (1 / 3) * Dist.dist (D.vertex x) (D.vertex y) := by
    have hmem : Dist.dist (D.vertex x) (D.vertex y) ∈
        insert (1 : ℝ) (vertDists x ∪ edgeDists x) :=
      Finset.mem_insert_of_mem <| Finset.mem_union_left _ <| Finset.mem_image.mpr
        ⟨y, Finset.mem_erase.mpr ⟨hyx, Finset.mem_univ _⟩, rfl⟩
    exact mul_le_mul_of_nonneg_left (Finset.min'_le _ _ hmem) (by norm_num)
  have hle_edge (x : V(G)) (e : E(G)) (he : ¬ G.Inc e.1 x.1) :
      r x ≤ (1 / 3) * infDist (D.vertex x) (range (D.edgePath e)) := by
    have hmem : infDist (D.vertex x) (range (D.edgePath e)) ∈
        insert (1 : ℝ) (vertDists x ∪ edgeDists x) :=
      Finset.mem_insert_of_mem <| Finset.mem_union_right _ <| Finset.mem_image.mpr
        ⟨e, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩, rfl⟩
    exact mul_le_mul_of_nonneg_left (Finset.min'_le _ _ hmem) (by norm_num)
  refine ⟨r, hpos, ?_, ?_⟩
  · intro x y hxy
    refine closedBall_disjoint_closedBall ?_
    have hd : 0 < Dist.dist (D.vertex x) (D.vertex y) :=
      mdist_pos.mpr (D.vertex_injective.ne hxy)
    have hx := hle_vert x y hxy.symm
    have hy := hle_vert y x hxy
    have : r x + r y ≤ (2 / 3) * Dist.dist (D.vertex x) (D.vertex y) := by
      calc
        r x + r y
            ≤ (1 / 3) * Dist.dist (D.vertex x) (D.vertex y) +
                (1 / 3) * Dist.dist (D.vertex y) (D.vertex x) := add_le_add hx hy
        _ = (2 / 3) * Dist.dist (D.vertex x) (D.vertex y) := by
          rw [mdist_comm (D.vertex y) (D.vertex x), ← two_mul, ← mul_assoc]
          norm_num
    exact lt_of_le_of_lt this <| (mul_lt_iff_lt_one_left hd).mpr two_thirds_lt_one
  · intro x z hz
    obtain ⟨hzball, hzsupp⟩ := hz
    rw [D.support_eq, mem_union, mem_iUnion] at hzsupp
    rcases hzsupp with ⟨y, rfl⟩ | ⟨e, he⟩
    · by_cases hyx : y = x
      · simp [hyx]
      · have hdist : Dist.dist (D.vertex x) (D.vertex y) ≤ r x := by
          rw [mdist_comm]
          exact Metric.mem_closedBall.mp hzball
        have : r x < Dist.dist (D.vertex x) (D.vertex y) := by
          have hxy : x ≠ y := fun h ↦ hyx h.symm
          have hlt : (1 / 3) * Dist.dist (D.vertex x) (D.vertex y) <
              Dist.dist (D.vertex x) (D.vertex y) :=
            (mul_lt_iff_lt_one_left
              (mdist_pos.mpr (D.vertex_injective.ne hxy))).mpr one_third_lt_one
          exact lt_of_le_of_lt (hle_vert x y hyx) hlt
        exact (this.not_ge hdist).elim
    · by_cases hinc : G.Inc e.1 x.1
      · exact Or.inr <| mem_biUnion (by exact hinc) he
      · have hdist : Dist.dist (D.vertex x) z ≤ r x := by
          rw [mdist_comm]
          exact Metric.mem_closedBall.mp hzball
        have hinf : infDist (D.vertex x) (range (D.edgePath e)) ≤ r x :=
          (infDist_le_dist_of_mem he).trans hdist
        have : r x < infDist (D.vertex x) (range (D.edgePath e)) :=
          lt_of_le_of_lt (hle_edge x e hinc) <|
            (mul_lt_iff_lt_one_left <|
              (hrange_closed e).notMem_iff_infDist_pos (hrange_nonempty e) |>.mp
                (D.vertex_notMem_range_edgePath_of_not_inc hinc)).mpr one_third_lt_one
        exact (this.not_ge hinf).elim

/-! ### Step 2: the middle of each cell -/

set_option linter.unusedSectionVars false in
/-- Last exit from `closedBall x rx` and first subsequent entry into `closedBall y ry` along a path
from `x` to `y`. Both parameter sets are closed and nonempty, so the extrema exist; disjointness of
the balls forces the exit time to precede the entry time and puts both endpoints on the spheres. -/
lemma exists_lastExit_firstEntry {x y : V} (γ : Path x y) {rx ry : ℝ}
    (hrx : 0 < rx) (hry : 0 < ry)
    (hdisj : Disjoint (closedBall x rx) (closedBall y ry)) :
    ∃ (t s : I), t < s ∧
      Dist.dist (γ t) x = rx ∧ Dist.dist (γ s) y = ry ∧
      (γ '' Icc t s) ∩ closedBall x rx = {γ t} ∧
      (γ '' Icc t s) ∩ closedBall y ry = {γ s} := by
  let Su : Set I := {u | γ u ∈ closedBall x rx}
  have hSu_closed : IsClosed Su := isClosed_closedBall.preimage γ.continuous
  have hSu_ne : Su.Nonempty := ⟨0, by
    change γ 0 ∈ closedBall x rx
    rw [γ.source]
    exact mem_closedBall_self (le_of_lt hrx)⟩
  obtain ⟨t, ht⟩ := hSu_closed.isCompact.exists_isGreatest hSu_ne
  let Sv : Set I := {u | t ≤ u ∧ γ u ∈ closedBall y ry}
  have hSv_closed : IsClosed Sv :=
    isClosed_Ici.inter (isClosed_closedBall.preimage γ.continuous)
  have hSv_ne : Sv.Nonempty := ⟨1, ⟨t.2.2, by
    rw [γ.target]
    exact mem_closedBall_self (le_of_lt hry)⟩⟩
  obtain ⟨s, hs⟩ := hSv_closed.isCompact.exists_isLeast hSv_ne
  have hts : t < s := by
    refine lt_of_le_of_ne hs.1.1 fun heq ↦ ?_
    exact hdisj.notMem_of_mem_left ht.1 (heq ▸ hs.1.2)
  refine ⟨t, s, hts, ?_, ?_, ?_, ?_⟩
  · have hle : Dist.dist (γ t) x ≤ rx := Metric.mem_closedBall.mp ht.1
    refine le_antisymm hle ?_
    by_contra hlt'
    have hlt : Dist.dist (γ t) x < rx := lt_of_not_ge hlt'
    have hcont : Continuous fun u : I ↦ Dist.dist (γ u) x :=
      Continuous.dist γ.continuous continuous_const
    have ht_ne_one : t ≠ 1 := by
      intro ht1
      have h1 : γ 1 ∈ closedBall x rx := by
        have := ht.1; rwa [ht1] at this
      have : y ∈ closedBall x rx := by rwa [γ.target] at h1
      exact hdisj.notMem_of_mem_left this (mem_closedBall_self (le_of_lt hry))
    have ht_lt : (t : ℝ) < 1 := unitInterval.lt_one_iff_ne_one.mpr ht_ne_one
    have hc := hcont.continuousAt (x := t)
    rw [Metric.continuousAt_iff] at hc
    obtain ⟨δ, δpos, hδ⟩ := hc (rx - Dist.dist (γ t) x) (sub_pos.mpr hlt)
    have hab : (t : ℝ) < min (t + δ / 2) 1 :=
      lt_min (lt_add_of_pos_right _ (half_pos δpos)) ht_lt
    obtain ⟨t0, ht0a, ht0b⟩ := exists_between hab
    have ht0I : t0 ∈ (I : Set ℝ) :=
      ⟨t.2.1.trans (le_of_lt ht0a), (le_of_lt ht0b).trans (min_le_right _ _)⟩
    set u : I := ⟨t0, ht0I⟩
    have hparamI : Dist.dist u t < δ := by
      have habs : Dist.dist t0 (t : ℝ) = t0 - t := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (le_of_lt ht0a))]
      have : t0 < t + δ / 2 := (lt_min_iff.mp ht0b).1
      change Dist.dist (u : ℝ) (t : ℝ) < δ
      linarith
    have hclose := hδ hparamI
    have hu_ball : Dist.dist (γ u) x < rx := by
      have := abs_lt.mp hclose; linarith
    have hu_mem : u ∈ Su := Metric.mem_closedBall.mpr (le_of_lt hu_ball)
    have : u ≤ t := ht.2 hu_mem
    exact (lt_of_le_of_lt this ht0a).false
  · have hle : Dist.dist (γ s) y ≤ ry := Metric.mem_closedBall.mp hs.1.2
    refine le_antisymm hle ?_
    by_contra hlt'
    have hlt : Dist.dist (γ s) y < ry := lt_of_not_ge hlt'
    have hcont : Continuous fun u : I ↦ Dist.dist (γ u) y :=
      Continuous.dist γ.continuous continuous_const
    have hc := hcont.continuousAt (x := s)
    rw [Metric.continuousAt_iff] at hc
    obtain ⟨δ, δpos, hδ⟩ := hc (ry - Dist.dist (γ s) y) (sub_pos.mpr hlt)
    have hε : 0 < min (δ / 2) (((s : ℝ) - t) / 2) :=
      lt_min (half_pos δpos) (half_pos (sub_pos.mpr hts))
    set t0 : ℝ := (s : ℝ) - min (δ / 2) (((s : ℝ) - t) / 2)
    have ht0_lt : t0 < s := sub_lt_self _ hε
    have ht0_gt : (t : ℝ) < t0 := by
      have : min (δ / 2) (((s : ℝ) - t) / 2) ≤ ((s : ℝ) - t) / 2 := min_le_right _ _
      linarith
    have ht0I : t0 ∈ (I : Set ℝ) :=
      ⟨t.2.1.trans (le_of_lt ht0_gt), (le_of_lt ht0_lt).trans s.2.2⟩
    set u : I := ⟨t0, ht0I⟩
    have hparamI : Dist.dist u s < δ := by
      have habs : Dist.dist t0 (s : ℝ) = s - t0 := by
        rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (le_of_lt ht0_lt))]
      have : s - t0 = min (δ / 2) (((s : ℝ) - t) / 2) := by simp [t0]
      change Dist.dist (u : ℝ) (s : ℝ) < δ
      calc Dist.dist t0 (s : ℝ)
          = min (δ / 2) (((s : ℝ) - t) / 2) := by rw [habs, this]
        _ ≤ δ / 2 := min_le_left _ _
        _ < δ := half_lt_self δpos
    have hclose := hδ hparamI
    have hu_ball : Dist.dist (γ u) y < ry := by
      have := abs_lt.mp hclose; linarith
    have hu_mem : u ∈ Sv := ⟨le_of_lt ht0_gt, Metric.mem_closedBall.mpr (le_of_lt hu_ball)⟩
    have : s ≤ u := hs.2 hu_mem
    exact (lt_of_le_of_lt this ht0_lt).false
  · ext z; constructor
    · intro hz
      obtain ⟨⟨u, hu, rfl⟩, hzB⟩ := hz
      have : u ≤ t := ht.2 hzB
      have : u = t := le_antisymm this hu.1
      simp [this]
    · intro hz
      rw [hz]
      exact ⟨⟨t, ⟨le_rfl, le_of_lt hts⟩, rfl⟩, ht.1⟩
  · ext z; constructor
    · intro hz
      obtain ⟨⟨u, hu, rfl⟩, hzB⟩ := hz
      have : s ≤ u := hs.2 ⟨hu.1, hzB⟩
      have : u = s := le_antisymm hu.2 this
      simp [this]
    · intro hz
      rw [hz]
      exact ⟨⟨s, ⟨le_of_lt hts, le_rfl⟩, rfl⟩, hs.1.2⟩

set_option linter.unusedSectionVars false in
/-- Distinct edge-path ranges meet only at images of shared endpoints. -/
lemma Drawing.range_edgePath_inter (D : Drawing G V) {e f : E(G)} (hef : e ≠ f) :
    range (D.edgePath e) ∩ range (D.edgePath f) ⊆
      {D.vertex (edgeSource e), D.vertex (edgeTarget e)} ∩
        {D.vertex (edgeSource f), D.vertex (edgeTarget f)} := by
  intro z ⟨⟨te, hte⟩, ⟨sf, hsf⟩⟩
  have hmem_ends : z = D.vertex (edgeSource e) ∨ z = D.vertex (edgeTarget e) := by
    by_cases hteI : te ∈ Ioo (0 : I) 1
    · have hinter : z ∈ pathInterior (D.edgePath e) := ⟨te, hteI, hte⟩
      have hnotV : z ∉ range D.vertex :=
        (D.pathInterior_edgePath_disjoint_vertex e).notMem_of_mem_left hinter
      have hnotF : z ∉ pathInterior (D.edgePath f) :=
        (D.pathInterior_edgePath_disjoint hef).notMem_of_mem_left hinter
      have hs01 : (sf : ℝ) = 0 ∨ (sf : ℝ) = 1 ∨ sf ∈ Ioo (0 : I) 1 := by
        have hs0 : 0 ≤ (sf : ℝ) := sf.2.1
        have hs1 : (sf : ℝ) ≤ 1 := sf.2.2
        rcases eq_or_lt_of_le hs0 with hs0' | hs0'
        · exact Or.inl hs0'.symm
        · rcases eq_or_lt_of_le hs1 with hs1' | hs1'
          · exact Or.inr (Or.inl hs1')
          · exact Or.inr (Or.inr ⟨hs0', hs1'⟩)
      rcases hs01 with hs0 | hs1 | hsI
      · exact (hnotV ⟨edgeSource f, by
          rw [← hsf, show sf = 0 from Subtype.ext hs0, Path.source]⟩).elim
      · exact (hnotV ⟨edgeTarget f, by
          rw [← hsf, show sf = 1 from Subtype.ext hs1, Path.target]⟩).elim
      · exact (hnotF ⟨sf, hsI, hsf⟩).elim
    · have ht01 : (te : ℝ) = 0 ∨ (te : ℝ) = 1 := by
        have ht0 : 0 ≤ (te : ℝ) := te.2.1
        have ht1 : (te : ℝ) ≤ 1 := te.2.2
        rw [mem_Ioo, not_and_or, not_lt, not_lt] at hteI
        rcases hteI with h0 | h1
        · exact Or.inl (le_antisymm h0 ht0)
        · exact Or.inr (le_antisymm ht1 h1)
      rcases ht01 with ht0 | ht1
      · left; rw [← hte, show te = 0 from Subtype.ext ht0, Path.source]
      · right; rw [← hte, show te = 1 from Subtype.ext ht1, Path.target]
  have hmem_ends' : z = D.vertex (edgeSource f) ∨ z = D.vertex (edgeTarget f) := by
    by_cases hsfI : sf ∈ Ioo (0 : I) 1
    · have hinter : z ∈ pathInterior (D.edgePath f) := ⟨sf, hsfI, hsf⟩
      have hnotV : z ∉ range D.vertex :=
        (D.pathInterior_edgePath_disjoint_vertex f).notMem_of_mem_left hinter
      have hnotE : z ∉ pathInterior (D.edgePath e) :=
        (D.pathInterior_edgePath_disjoint (Ne.symm hef)).notMem_of_mem_left hinter
      have ht01 : (te : ℝ) = 0 ∨ (te : ℝ) = 1 ∨ te ∈ Ioo (0 : I) 1 := by
        have ht0 : 0 ≤ (te : ℝ) := te.2.1
        have ht1 : (te : ℝ) ≤ 1 := te.2.2
        rcases eq_or_lt_of_le ht0 with ht0' | ht0'
        · exact Or.inl ht0'.symm
        · rcases eq_or_lt_of_le ht1 with ht1' | ht1'
          · exact Or.inr (Or.inl ht1')
          · exact Or.inr (Or.inr ⟨ht0', ht1'⟩)
      rcases ht01 with ht0 | ht1 | htI
      · exact (hnotV ⟨edgeSource e, by
          rw [← hte, show te = 0 from Subtype.ext ht0, Path.source]⟩).elim
      · exact (hnotV ⟨edgeTarget e, by
          rw [← hte, show te = 1 from Subtype.ext ht1, Path.target]⟩).elim
      · exact (hnotE ⟨te, htI, hte⟩).elim
    · have hs01 : (sf : ℝ) = 0 ∨ (sf : ℝ) = 1 := by
        have hs0 : 0 ≤ (sf : ℝ) := sf.2.1
        have hs1 : (sf : ℝ) ≤ 1 := sf.2.2
        rw [mem_Ioo, not_and_or, not_lt, not_lt] at hsfI
        rcases hsfI with h0 | h1
        · exact Or.inl (le_antisymm h0 hs0)
        · exact Or.inr (le_antisymm hs1 h1)
      rcases hs01 with hs0 | hs1
      · left; rw [← hsf, show sf = 0 from Subtype.ext hs0, Path.source]
      · right; rw [← hsf, show sf = 1 from Subtype.ext hs1, Path.target]
  refine ⟨?_, ?_⟩
  · simpa [mem_insert_iff, mem_singleton_iff] using hmem_ends
  · simpa [mem_insert_iff, mem_singleton_iff] using hmem_ends'

/-- The middles of the cells: for each edge, the part of its cell running from its last exit from
the ball at one end to its first entry into the ball at the other. Distinct middles are disjoint,
each avoids the balls at all vertices other than its own two ends, and each meets those two balls in
exactly its two endpoints, which lie on the spheres.

Stated as a family rather than one edge at a time because the disjointness across edges is what the
next step consumes. The middle is presented as a path rather than as a set so that it can be fed to
the approximation lemma. -/
theorem Drawing.exists_middlePaths [G.Finite] [G.Loopless] (D : Drawing G V) {r : V(G) → ℝ}
    (hpos : ∀ x, 0 < r x)
    (hdisj : Pairwise fun x y ↦ Disjoint (closedBall (D.vertex x) (r x))
      (closedBall (D.vertex y) (r y)))
    (hball : ∀ x, closedBall (D.vertex x) (r x) ∩ D.support ⊆
      {D.vertex x} ∪ ⋃ e ∈ {e : E(G) | G.Inc e.1 x.1}, range (D.edgePath e)) :
    ∃ (a b : E(G) → V) (Q : ∀ e, Path (a e) (b e)),
      (∀ e, range (Q e) ⊆ range (D.edgePath e)) ∧
      (∀ e, dist (a e) (D.vertex (edgeSource e)) = r (edgeSource e)) ∧
      (∀ e, dist (b e) (D.vertex (edgeTarget e)) = r (edgeTarget e)) ∧
      (∀ e, range (Q e) ∩ closedBall (D.vertex (edgeSource e)) (r (edgeSource e)) = {a e}) ∧
      (∀ e, range (Q e) ∩ closedBall (D.vertex (edgeTarget e)) (r (edgeTarget e)) = {b e}) ∧
      (∀ e, ∀ x, x ≠ edgeSource e → x ≠ edgeTarget e →
        Disjoint (range (Q e)) (closedBall (D.vertex x) (r x))) ∧
      Pairwise fun e f ↦ Disjoint (range (Q e)) (range (Q f)) := by
  classical
  have hsrc_ne_tgt (e : E(G)) : edgeSource e ≠ edgeTarget e := by
    intro heq
    exact (isLink_edgeSource_edgeTarget e).ne (congrArg Subtype.val heq)
  have hinc_ends (e : E(G)) {x : V(G)} (hx : G.Inc e.1 x.1) :
      x = edgeSource e ∨ x = edgeTarget e := by
    have h := hx.eq_or_eq_of_isLink (isLink_edgeSource_edgeTarget e)
    exact h.imp (fun h ↦ Subtype.ext h) (fun h ↦ Subtype.ext h)
  choose t_e s_e ht_lt hdist_a hdist_b hinter_a hinter_b using fun e : E(G) ↦
    exists_lastExit_firstEntry (D.edgePath e) (hpos _) (hpos _) (hdisj (hsrc_ne_tgt e))
  have ht_le (e : E(G)) : t_e e ≤ s_e e := le_of_lt (ht_lt e)
  let a : E(G) → V := fun e ↦ D.edgePath e (t_e e)
  let b : E(G) → V := fun e ↦ D.edgePath e (s_e e)
  let Q : ∀ e, Path (a e) (b e) := fun e ↦ (D.edgePath e).subpath (t_e e) (s_e e)
  have hQ_range (e : E(G)) : range (Q e) = D.edgePath e '' Icc (t_e e) (s_e e) :=
    Path.range_subpath_of_le _ _ _ (ht_le e)
  have hQ_subset (e : E(G)) : range (Q e) ⊆ range (D.edgePath e) := by
    rw [hQ_range]; exact image_subset_range _ _
  have hmeet_a (e : E(G)) :
      range (Q e) ∩ closedBall (D.vertex (edgeSource e)) (r (edgeSource e)) = {a e} := by
    rw [hQ_range, show a e = D.edgePath e (t_e e) from rfl]
    exact hinter_a e
  have hmeet_b (e : E(G)) :
      range (Q e) ∩ closedBall (D.vertex (edgeTarget e)) (r (edgeTarget e)) = {b e} := by
    rw [hQ_range, show b e = D.edgePath e (s_e e) from rfl]
    exact hinter_b e
  refine ⟨a, b, Q, hQ_subset, hdist_a, hdist_b, hmeet_a, hmeet_b, ?_, ?_⟩
  · intro e x hxu hxv
    refine disjoint_left.mpr ?_
    intro z hzQ hzB
    have hzsupp : z ∈ D.support := D.edgePath_range_subset_support e (hQ_subset e hzQ)
    have hzmem := hball x ⟨hzB, hzsupp⟩
    rw [mem_union, mem_singleton_iff] at hzmem
    rcases hzmem with rfl | hzE
    · exact D.vertex_notMem_range_edgePath_of_not_inc
        (fun hinc ↦ (hinc_ends e hinc).elim hxu hxv) (hQ_subset e hzQ)
    · obtain ⟨f, hf, hzf⟩ := mem_iUnion₂.mp hzE
      have hfinc : G.Inc f.1 x.1 := hf
      by_cases hef : f = e
      · have hfinc' : G.Inc e.1 x.1 := by simpa [hef] using hfinc
        exact (hinc_ends e hfinc').elim hxu hxv
      · have hz_inter :=
          (D.range_edgePath_inter (Ne.symm hef)) ⟨hQ_subset e hzQ, hzf⟩
        have hz_end : z = D.vertex (edgeSource e) ∨ z = D.vertex (edgeTarget e) := by
          simpa [mem_inter_iff, mem_insert_iff, mem_singleton_iff] using hz_inter.1
        rcases hz_end with rfl | rfl
        · exact (hdisj hxu.symm).notMem_of_mem_left
            (mem_closedBall_self (le_of_lt (hpos _))) hzB
        · exact (hdisj hxv.symm).notMem_of_mem_left
            (mem_closedBall_self (le_of_lt (hpos _))) hzB
  · intro e f hef
    refine disjoint_left.mpr ?_
    intro z hze hzf
    have hz_inter := (D.range_edgePath_inter hef) ⟨hQ_subset e hze, hQ_subset f hzf⟩
    have hz_end : z = D.vertex (edgeSource e) ∨ z = D.vertex (edgeTarget e) := by
      simpa [mem_inter_iff, mem_insert_iff, mem_singleton_iff] using hz_inter.1
    have ha_ne : a e ≠ D.vertex (edgeSource e) := by
      intro h
      have : Dist.dist (a e) (D.vertex (edgeSource e)) = 0 := by simp [h]
      exact (hpos _).ne' (hdist_a e ▸ this)
    have hb_ne : b e ≠ D.vertex (edgeTarget e) := by
      intro h
      have : Dist.dist (b e) (D.vertex (edgeTarget e)) = 0 := by simp [h]
      exact (hpos _).ne' (hdist_b e ▸ this)
    rcases hz_end with hz | hz
    · have : z ∈ range (Q e) ∩ closedBall (D.vertex (edgeSource e)) (r (edgeSource e)) :=
        ⟨hze, by rw [hz]; exact mem_closedBall_self (le_of_lt (hpos _))⟩
      rw [hmeet_a, mem_singleton_iff, hz] at this
      exact ha_ne this.symm
    · have : z ∈ range (Q e) ∩ closedBall (D.vertex (edgeTarget e)) (r (edgeTarget e)) :=
        ⟨hze, by rw [hz]; exact mem_closedBall_self (le_of_lt (hpos _))⟩
      rw [hmeet_b, mem_singleton_iff, hz] at this
      exact hb_ne this.symm

/-! ### Step 3: simultaneous polygonal approximation -/

set_option linter.unusedSectionVars false in
/-- Compact/closed separation as a real lower bound on metric distances
(`Graph.dist` shadows the metric `dist` in this namespace). -/
private lemma exists_pos_le_dist_of_disjoint {s t : Set V}
    (hs : IsCompact s) (ht : IsClosed t) (hst : Disjoint s t) :
    ∃ r : ℝ, 0 < r ∧ ∀ x ∈ s, ∀ y ∈ t, r ≤ Dist.dist x y := by
  rcases s.eq_empty_or_nonempty with rfl | hsne
  · exact ⟨1, one_pos, by simp⟩
  rcases t.eq_empty_or_nonempty with rfl | htne
  · exact ⟨1, one_pos, by simp⟩
  obtain ⟨x, hx, hmin⟩ := hs.exists_isMinOn hsne (continuous_infDist_pt (s := t)).continuousOn
  have hpos : 0 < infDist x t :=
    (ht.notMem_iff_infDist_pos htne).mp (hst.notMem_of_mem_left hx)
  refine ⟨infDist x t, hpos, fun y hy z hz => ?_⟩
  exact (hmin hy).trans (infDist_le_dist_of_mem hz)

/-- Finitely many pairwise disjoint paths, each disjoint from a closed set of its own, can be
replaced by polygonal paths with the same endpoints, still pairwise disjoint and still avoiding
those closed sets.

This is Status.md's Steps 3 and 4 together, with the separation constant `δ` internal to the proof:
the ranges are compact and pairwise disjoint, and there are finitely many of them, so their pairwise
distances and their distances to the `K i` have a positive lower bound, and
`Path.exists_polygonalPath_of_thickening` at a third of it keeps everything apart. Nothing about
graphs enters. -/
theorem exists_polygonalPath_family_of_disjoint {ι : Type*} [Finite ι] {a b : ι → V}
    (Q : ∀ i, Path (a i) (b i)) (hQ : Pairwise fun i j ↦ Disjoint (range (Q i)) (range (Q j)))
    (K : ι → Set V) (hK : ∀ i, IsClosed (K i)) (hQK : ∀ i, Disjoint (range (Q i)) (K i)) :
    ∃ P : ∀ i, PolygonalPath (a i) (b i),
      (Pairwise fun i j ↦ Disjoint (P i).toSet (P j).toSet) ∧ ∀ i, Disjoint (P i).toSet (K i) := by
  classical
  -- `Graph.dist` / `Graph.dist_comm` / `Graph.dist_triangle` shadow the metric versions.
  have mdist_comm (x y : V) : Dist.dist x y = Dist.dist y x :=
    PseudoMetricSpace.dist_comm x y
  have mdist_triangle (x y z : V) :
      Dist.dist x z ≤ Dist.dist x y + Dist.dist y z :=
    @_root_.dist_triangle V _ x y z
  have : Fintype ι := Fintype.ofFinite _
  have hrange_nonempty (i : ι) : (range (Q i)).Nonempty := ⟨_, ⟨0, rfl⟩⟩
  have hrange_compact (i : ι) : IsCompact (range (Q i)) := isCompact_range (Q i).continuous
  have hrange_closed (i : ι) : IsClosed (range (Q i)) := (hrange_compact i).isClosed
  -- Status.md: empty minima default to `1`, encoded by adjoining `1` to the finite set of separations.
  let pairSep (i j : ι) (hij : i ≠ j) : ℝ :=
    Classical.choose <|
      exists_pos_le_dist_of_disjoint (hrange_compact i) (hrange_closed j) (hQ hij)
  let kSep (i : ι) : ℝ :=
    Classical.choose <|
      exists_pos_le_dist_of_disjoint (hrange_compact i) (hK i) (hQK i)
  have hpairSep_spec (i j : ι) (hij : i ≠ j) :
      0 < pairSep i j hij ∧
        ∀ x ∈ range (Q i), ∀ y ∈ range (Q j), pairSep i j hij ≤ Dist.dist x y :=
    Classical.choose_spec <|
      exists_pos_le_dist_of_disjoint (hrange_compact i) (hrange_closed j) (hQ hij)
  have hkSep_spec (i : ι) :
      0 < kSep i ∧ ∀ x ∈ range (Q i), ∀ y ∈ K i, kSep i ≤ Dist.dist x y :=
    Classical.choose_spec <|
      exists_pos_le_dist_of_disjoint (hrange_compact i) (hK i) (hQK i)
  let seps : Finset ℝ :=
    insert (1 : ℝ)
      ((Finset.univ.biUnion fun i =>
          Finset.univ.biUnion fun j => if h : i ≠ j then {pairSep i j h} else ∅) ∪
        Finset.univ.image kSep)
  let δ : ℝ := (1 / 3) * seps.min' (Finset.insert_nonempty _ _)
  have hδpos : 0 < δ := by
    refine mul_pos (by norm_num) ?_
    rw [Finset.lt_min'_iff]
    intro d hd
    rw [Finset.mem_insert, Finset.mem_union] at hd
    rcases hd with rfl | hpair | hk
    · exact one_pos
    · obtain ⟨i, _, hj⟩ := Finset.mem_biUnion.mp hpair
      obtain ⟨j, _, hd⟩ := Finset.mem_biUnion.mp hj
      split_ifs at hd with hij
      · rw [Finset.mem_singleton] at hd
        exact hd ▸ (hpairSep_spec i j hij).1
      · exact (Finset.notMem_empty _ hd).elim
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hk
      exact (hkSep_spec i).1
  have hδ_le_pair (i j : ι) (hij : i ≠ j) : δ ≤ (1 / 3) * pairSep i j hij := by
    have hmem : pairSep i j hij ∈ seps :=
      Finset.mem_insert_of_mem <| Finset.mem_union_left _ <| Finset.mem_biUnion.mpr
        ⟨i, Finset.mem_univ _, Finset.mem_biUnion.mpr
          ⟨j, Finset.mem_univ _, by simp [hij]⟩⟩
    exact mul_le_mul_of_nonneg_left (Finset.min'_le _ _ hmem) (by norm_num)
  have hδ_le_k (i : ι) : δ ≤ (1 / 3) * kSep i := by
    have hmem : kSep i ∈ seps :=
      Finset.mem_insert_of_mem <| Finset.mem_union_right _ <|
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    exact mul_le_mul_of_nonneg_left (Finset.min'_le _ _ hmem) (by norm_num)
  choose P hP using fun i => (Q i).exists_polygonalPath_of_thickening hδpos
  refine ⟨P, ?_, ?_⟩
  · intro i j hij
    refine Disjoint.mono (hP i) (hP j) ?_
    refine disjoint_iff_inf_le.mpr ?_
    intro z ⟨hzi, hzj⟩
    have hzi' := (Metric.mem_thickening_iff_infDist_lt (hrange_nonempty i)).mp hzi
    have hzj' := (Metric.mem_thickening_iff_infDist_lt (hrange_nonempty j)).mp hzj
    obtain ⟨x, hx, hxz⟩ := (infDist_lt_iff (hrange_nonempty i)).mp hzi'
    obtain ⟨y, hy, hyz⟩ := (infDist_lt_iff (hrange_nonempty j)).mp hzj'
    have hsep := (hpairSep_spec i j hij).2 x hx y hy
    have hlt : Dist.dist x y < pairSep i j hij := by
      have : Dist.dist x y < 2 * δ :=
        calc
          Dist.dist x y ≤ Dist.dist x z + Dist.dist z y := mdist_triangle x z y
          _ = Dist.dist z x + Dist.dist z y := by rw [mdist_comm x z]
          _ < δ + δ := add_lt_add hxz hyz
          _ = 2 * δ := by ring
      have h2 : 2 * δ ≤ (2 / 3) * pairSep i j hij := by
        have := hδ_le_pair i j hij
        nlinarith
      have h23 : (2 / 3 : ℝ) * pairSep i j hij < pairSep i j hij :=
        (mul_lt_iff_lt_one_left (hpairSep_spec i j hij).1).mpr (by norm_num)
      exact this.trans <| lt_of_le_of_lt h2 h23
    exact (hlt.not_ge hsep).elim
  · intro i
    refine Disjoint.mono_left (hP i) ?_
    refine disjoint_iff_inf_le.mpr ?_
    intro z ⟨hzP, hzK⟩
    have hz' := (Metric.mem_thickening_iff_infDist_lt (hrange_nonempty i)).mp hzP
    obtain ⟨x, hx, hxz⟩ := (infDist_lt_iff (hrange_nonempty i)).mp hz'
    have hsep := (hkSep_spec i).2 x hx z hzK
    have hlt : Dist.dist x z < kSep i := by
      have : Dist.dist x z < δ := by
        rwa [mdist_comm]
      exact this.trans_le <|
        (hδ_le_k i).trans <|
          le_of_lt <| (mul_lt_iff_lt_one_left (hkSep_spec i).1).mpr (by norm_num : (1 / 3 : ℝ) < 1)
    exact (hlt.not_ge hsep).elim

/-! ### Step 4: re-cutting and straightening -/

open PolygonalPath

/-- In a normed space, a point of the radius `[c, z]` with `‖z - c‖ = r` is determined by its
distance to `c`. -/
private lemma eq_endpoint_of_mem_segment_of_dist_eq {c z w : V} {r : ℝ} (hr : 0 < r)
    (hz : Dist.dist z c = r) (hw : w ∈ segment ℝ c z) (hwr : Dist.dist w c = r) : w = z := by
  obtain ⟨t, ⟨ht0, _⟩, rfl⟩ := (segment_eq_image_lineMap (𝕜 := ℝ) c z).symm ▸ hw
  have hdist : Dist.dist (AffineMap.lineMap c z t) c = t * r := by
    rw [dist_eq_norm, AffineMap.lineMap_apply]
    simp only [vadd_eq_add, vsub_eq_sub]
    rw [add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0,
      ← dist_eq_norm, hz]
  exact (mul_eq_right₀ hr.ne').mp (hdist.symm.trans hwr) ▸ by simp

/-- The closed radius minus the open ball is exactly the sphere endpoint. -/
private lemma segment_diff_ball_eq_singleton {c z : V} {r : ℝ} (hr : 0 < r)
    (hz : Dist.dist z c = r) : segment ℝ c z \ ball c r = {z} := by
  refine subset_antisymm ?_ ?_
  · intro w hw
    have hwseg : w ∈ segment ℝ c z := hw.1
    have hwr : r ≤ Dist.dist w c := by simpa [mem_ball, not_lt] using hw.2
    exact eq_endpoint_of_mem_segment_of_dist_eq hr hz hwseg <|
      le_antisymm
        (mem_closedBall.mp <| (convex_closedBall c r).segment_subset
          (mem_closedBall_self hr.le) (mem_closedBall.mpr hz.le) hwseg) hwr
  · intro w hw
    rw [mem_singleton_iff] at hw
    subst w
    refine ⟨right_mem_segment ℝ c z, ?_⟩
    simpa [mem_ball, not_lt, PseudoMetricSpace.dist_comm z c] using hz.symm.le

/-- On an embedded polygonal arc, cutting at `P.toPath t₀` recovers the two parameter subarcs. -/
private lemma IsSimple.toSet_breakAt_eq {x y a : V} {P : PolygonalPath x y}
    (hP : P.IsSimple) (hlen : 0 < P.length) (ha : a ∈ P.toSet) {t₀ : I}
    (ht₀ : P.toPath t₀ = a) :
    (P.breakAt ha).1.toSet = P.toPath '' Icc (0 : I) t₀ ∧
    (P.breakAt ha).2.toSet = P.toPath '' Icc t₀ (1 : I) := by
  have hinj : Injective P.toPath := (injective_toPath_iff P).mpr ⟨hP, hlen⟩
  have hembed : IsClosedEmbedding P.toPath :=
    P.toPath.continuous.isClosedEmbedding hinj
  obtain ⟨_, _, hAB⟩ := hP.breakAt ha
  have hunion := P.breakAt_toSet_union (ha := ha)
  have hAsub : (P.breakAt ha).1.toSet ⊆ range P.toPath := by
    rw [← P.toSet_eq_range_toPath, ← hunion]; exact subset_union_left
  have hBsub : (P.breakAt ha).2.toSet ⊆ range P.toPath := by
    rw [← P.toSet_eq_range_toPath, ← hunion]; exact subset_union_right
  have hApre : IsConnected (P.toPath ⁻¹' (P.breakAt ha).1.toSet) :=
    (P.breakAt ha).1.isConnected_toSet.preimage_of_isClosedMap hinj hembed.isClosedMap hAsub
  have hBpre : IsConnected (P.toPath ⁻¹' (P.breakAt ha).2.toSet) :=
    (P.breakAt ha).2.isConnected_toSet.preimage_of_isClosedMap hinj hembed.isClosedMap hBsub
  have h0A : (0 : I) ∈ P.toPath ⁻¹' (P.breakAt ha).1.toSet := by simp [Path.source]
  have ht0A : t₀ ∈ P.toPath ⁻¹' (P.breakAt ha).1.toSet := by simp [ht₀]
  have ht0B : t₀ ∈ P.toPath ⁻¹' (P.breakAt ha).2.toSet := by simp [ht₀]
  have h1B : (1 : I) ∈ P.toPath ⁻¹' (P.breakAt ha).2.toSet := by simp [Path.target]
  have hAIcc : Icc (0 : ℝ) ↑t₀ ⊆ (↑) '' (P.toPath ⁻¹' (P.breakAt ha).1.toSet) :=
    (hApre.image _ continuous_subtype_val.continuousOn).Icc_subset
      (mem_image_of_mem _ h0A) (mem_image_of_mem _ ht0A)
  have hBIcc : Icc ↑t₀ (1 : ℝ) ⊆ (↑) '' (P.toPath ⁻¹' (P.breakAt ha).2.toSet) :=
    (hBpre.image _ continuous_subtype_val.continuousOn).Icc_subset
      (mem_image_of_mem _ ht0B) (mem_image_of_mem _ h1B)
  refine ⟨subset_antisymm ?_ ?_, subset_antisymm ?_ ?_⟩
  · intro w hw
    obtain ⟨t, rfl⟩ : w ∈ range P.toPath := by
      have : w ∈ P.toSet := hunion ▸ Or.inl hw
      rwa [P.toSet_eq_range_toPath] at this
    refine ⟨t, ⟨bot_le, ?_⟩, rfl⟩
    by_contra ht
    have ht' : t₀ < t := lt_of_not_ge ht
    obtain ⟨s, hs, hseq⟩ := hBIcc ⟨ht'.le, t.2.2⟩
    have hinter : P.toPath t ∈ (P.breakAt ha).1.toSet ∩ (P.breakAt ha).2.toSet :=
      ⟨hw, (Subtype.ext hseq) ▸ hs⟩
    rw [hAB, mem_singleton_iff] at hinter
    exact ht'.ne' (hinj (hinter.trans ht₀.symm))
  · rintro w ⟨t, ht, rfl⟩
    obtain ⟨s, hs, hseq⟩ := hAIcc ⟨t.2.1, ht.2⟩
    exact (Subtype.ext hseq) ▸ hs
  · intro w hw
    obtain ⟨t, rfl⟩ : w ∈ range P.toPath := by
      have : w ∈ P.toSet := hunion ▸ Or.inr hw
      rwa [P.toSet_eq_range_toPath] at this
    refine ⟨t, ⟨?_, le_top⟩, rfl⟩
    by_contra ht
    have ht' : t < t₀ := lt_of_not_ge ht
    obtain ⟨s, hs, hseq⟩ := hAIcc ⟨t.2.1, ht'.le⟩
    have hinter : P.toPath t ∈ (P.breakAt ha).1.toSet ∩ (P.breakAt ha).2.toSet :=
      ⟨(Subtype.ext hseq) ▸ hs, hw⟩
    rw [hAB, mem_singleton_iff] at hinter
    exact ht'.ne (hinj (hinter.trans ht₀.symm))
  · rintro w ⟨t, ht, rfl⟩
    obtain ⟨s, hs, hseq⟩ := hBIcc ⟨ht.1, t.2.2⟩
    exact (Subtype.ext hseq) ▸ hs

private lemma exists_lastExit_firstEntry_of_mem {a b c d : V} (γ : Path a b) {rc rd : ℝ}
    (hdisj : Disjoint (closedBall c rc) (closedBall d rd))
    (ha : a ∈ closedBall c rc) (hb : b ∈ closedBall d rd) :
    ∃ (t s : I), t < s ∧
      Dist.dist (γ t) c = rc ∧ Dist.dist (γ s) d = rd ∧
      (γ '' Icc t s) ∩ closedBall c rc = {γ t} ∧
      (γ '' Icc t s) ∩ closedBall d rd = {γ s} := by
  let Su : Set I := {u | γ u ∈ closedBall c rc}
  have hSu_closed : IsClosed Su := isClosed_closedBall.preimage γ.continuous
  have hSu_ne : Su.Nonempty := ⟨0, by simpa [Su, Path.source] using ha⟩
  obtain ⟨t, ht⟩ := hSu_closed.isCompact.exists_isGreatest hSu_ne
  let Sv : Set I := {u | t ≤ u ∧ γ u ∈ closedBall d rd}
  have hSv_closed : IsClosed Sv :=
    isClosed_Ici.inter (isClosed_closedBall.preimage γ.continuous)
  have hSv_ne : Sv.Nonempty := ⟨1, ⟨t.2.2, by simpa [Path.target] using hb⟩⟩
  obtain ⟨s, hs⟩ := hSv_closed.isCompact.exists_isLeast hSv_ne
  have hts : t < s := by
    refine lt_of_le_of_ne hs.1.1 fun heq ↦ ?_
    exact hdisj.notMem_of_mem_left ht.1 (heq ▸ hs.1.2)
  refine ⟨t, s, hts, ?_, ?_, ?_, ?_⟩
  · have hle : Dist.dist (γ t) c ≤ rc := Metric.mem_closedBall.mp ht.1
    refine le_antisymm hle ?_
    by_contra hlt'
    have hlt : Dist.dist (γ t) c < rc := lt_of_not_ge hlt'
    have hcont : Continuous fun u : I ↦ Dist.dist (γ u) c :=
      Continuous.dist γ.continuous continuous_const
    have ht_ne_one : t ≠ 1 := by
      intro ht1
      have hmem : γ 1 ∈ closedBall c rc := by
        have := ht.1; rwa [ht1] at this
      have : b ∈ closedBall c rc := by rwa [γ.target] at hmem
      exact hdisj.notMem_of_mem_left this hb
    have ht_lt : (t : ℝ) < 1 := unitInterval.lt_one_iff_ne_one.mpr ht_ne_one
    have hc := hcont.continuousAt (x := t)
    rw [Metric.continuousAt_iff] at hc
    obtain ⟨δ, δpos, hδ⟩ := hc (rc - Dist.dist (γ t) c) (sub_pos.mpr hlt)
    have hab : (t : ℝ) < min (t + δ / 2) 1 :=
      lt_min (lt_add_of_pos_right _ (half_pos δpos)) ht_lt
    obtain ⟨t0, ht0a, ht0b⟩ := exists_between hab
    have ht0I : t0 ∈ (I : Set ℝ) :=
      ⟨t.2.1.trans (le_of_lt ht0a), (le_of_lt ht0b).trans (min_le_right _ _)⟩
    set u : I := ⟨t0, ht0I⟩
    have hparamI : Dist.dist u t < δ := by
      have habs : Dist.dist t0 (t : ℝ) = t0 - t := by
        rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr (le_of_lt ht0a))]
      have : t0 < t + δ / 2 := (lt_min_iff.mp ht0b).1
      change Dist.dist (u : ℝ) (t : ℝ) < δ
      linarith
    have hclose := hδ hparamI
    have hu_ball : Dist.dist (γ u) c < rc := by
      have := abs_lt.mp hclose; linarith
    have hu_mem : u ∈ Su := Metric.mem_closedBall.mpr (le_of_lt hu_ball)
    have : u ≤ t := ht.2 hu_mem
    exact (lt_of_le_of_lt this ht0a).false
  · have hle : Dist.dist (γ s) d ≤ rd := Metric.mem_closedBall.mp hs.1.2
    refine le_antisymm hle ?_
    by_contra hlt'
    have hlt : Dist.dist (γ s) d < rd := lt_of_not_ge hlt'
    have hcont : Continuous fun u : I ↦ Dist.dist (γ u) d :=
      Continuous.dist γ.continuous continuous_const
    have hc := hcont.continuousAt (x := s)
    rw [Metric.continuousAt_iff] at hc
    obtain ⟨δ, δpos, hδ⟩ := hc (rd - Dist.dist (γ s) d) (sub_pos.mpr hlt)
    have hε : 0 < min (δ / 2) (((s : ℝ) - t) / 2) :=
      lt_min (half_pos δpos) (half_pos (sub_pos.mpr hts))
    set t0 : ℝ := (s : ℝ) - min (δ / 2) (((s : ℝ) - t) / 2)
    have ht0_lt : t0 < s := sub_lt_self _ hε
    have ht0_gt : (t : ℝ) < t0 := by
      have : min (δ / 2) (((s : ℝ) - t) / 2) ≤ ((s : ℝ) - t) / 2 := min_le_right _ _
      linarith
    have ht0I : t0 ∈ (I : Set ℝ) :=
      ⟨t.2.1.trans (le_of_lt ht0_gt), (le_of_lt ht0_lt).trans s.2.2⟩
    set u : I := ⟨t0, ht0I⟩
    have hparamI : Dist.dist u s < δ := by
      have habs : Dist.dist t0 (s : ℝ) = s - t0 := by
        rw [Real.dist_eq, abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr (le_of_lt ht0_lt))]
      have : s - t0 = min (δ / 2) (((s : ℝ) - t) / 2) := by simp [t0]
      change Dist.dist (u : ℝ) (s : ℝ) < δ
      calc Dist.dist t0 (s : ℝ)
          = min (δ / 2) (((s : ℝ) - t) / 2) := by rw [habs, this]
        _ ≤ δ / 2 := min_le_left _ _
        _ < δ := half_lt_self δpos
    have hclose := hδ hparamI
    have hu_ball : Dist.dist (γ u) d < rd := by
      have := abs_lt.mp hclose; linarith
    have hu_mem : u ∈ Sv := ⟨le_of_lt ht0_gt, Metric.mem_closedBall.mpr (le_of_lt hu_ball)⟩
    have : s ≤ u := hs.2 hu_mem
    exact (lt_of_le_of_lt this ht0_lt).false
  · ext z; constructor
    · intro hz
      obtain ⟨⟨u, hu, rfl⟩, hzB⟩ := hz
      have : u ≤ t := ht.2 hzB
      have : u = t := le_antisymm this hu.1
      simp [this]
    · intro hz
      rw [hz]
      exact ⟨⟨t, ⟨le_rfl, le_of_lt hts⟩, rfl⟩, ht.1⟩
  · ext z; constructor
    · intro hz
      obtain ⟨⟨u, hu, rfl⟩, hzB⟩ := hz
      have : s ≤ u := hs.2 ⟨hu.1, hzB⟩
      have : u = s := le_antisymm hu.2 this
      simp [this]
    · intro hz
      rw [hz]
      exact ⟨⟨s, ⟨le_of_lt hts, le_rfl⟩, rfl⟩, hs.1.2⟩

theorem exists_isSimple_radial {cu cv : V} {ru rv : ℝ} (hru : 0 < ru) (hrv : 0 < rv)
    (hballs : Disjoint (closedBall cu ru) (closedBall cv rv)) {x y : V}
    (P : PolygonalPath x y) (hx : x ∈ closedBall cu ru) (hy : y ∈ closedBall cv rv) :
    ∃ (zu zv : V) (R : PolygonalPath cu cv), R.IsSimple ∧
      dist zu cu = ru ∧ dist zv cv = rv ∧
      R.toSet ∩ closedBall cu ru = segment ℝ cu zu ∧
      R.toSet ∩ closedBall cv rv = segment ℝ cv zv ∧
      R.toSet \ (ball cu ru ∪ ball cv rv) ⊆ P.toSet := by
  have mdist_comm (p q : V) : Dist.dist p q = Dist.dist q p :=
    PseudoMetricSpace.dist_comm p q
  have hBu {z : V} (hz : Dist.dist z cu = ru) :
      segment ℝ cu z ⊆ closedBall cu ru :=
    (convex_closedBall cu ru).segment_subset (mem_closedBall_self hru.le)
      (mem_closedBall.mpr hz.le)
  have hBv {z : V} (hz : Dist.dist z cv = rv) :
      segment ℝ cv z ⊆ closedBall cv rv :=
    (convex_closedBall cv rv).segment_subset (mem_closedBall_self hrv.le)
      (mem_closedBall.mpr hz.le)
  have hxy : x ≠ y := fun h ↦ hballs.notMem_of_mem_left hx (h ▸ hy)
  obtain ⟨M, hM, hMP⟩ := P.exists_isSimple_toSet_subset
  have hMlen : 0 < M.length := M.length_pos_of_ne hxy
  have hinj : Injective M.toPath := (injective_toPath_iff M).mpr ⟨hM, hMlen⟩
  obtain ⟨τ, τv, hτlt, hzu_dist, hzv_dist, hmid_u, hmid_v⟩ :=
    exists_lastExit_firstEntry_of_mem M.toPath hballs hx hy
  set zu : V := M.toPath τ
  set zv : V := M.toPath τv
  have hzu_toSet : zu ∈ M.toSet := by rw [M.toSet_eq_range_toPath]; exact ⟨τ, rfl⟩
  obtain ⟨_, hBsimple, _⟩ := hM.breakAt hzu_toSet
  set B := (M.breakAt hzu_toSet).2
  have hB_eq : B.toSet = M.toPath '' Icc τ (1 : I) :=
    (IsSimple.toSet_breakAt_eq hM hMlen hzu_toSet rfl).2
  have hBlen : 0 < B.length := B.length_pos_of_ne fun h ↦
    hballs.notMem_of_mem_left (mem_closedBall.mpr hzu_dist.le) (by simpa [← h] using hy)
  have hB_subset_M : B.toSet ⊆ M.toSet := by
    rw [← breakAt_toSet_union (P := M) (ha := hzu_toSet)]; exact subset_union_right
  have hzv_toSet : zv ∈ B.toSet := by
    rw [hB_eq]; exact ⟨τv, ⟨hτlt.le, le_top⟩, rfl⟩
  obtain ⟨hQsimple, _, hQB⟩ := hBsimple.breakAt hzv_toSet
  set Q := (B.breakAt hzv_toSet).1
  have hQ_subset_B : Q.toSet ⊆ B.toSet := by
    rw [← breakAt_toSet_union (P := B) (ha := hzv_toSet)]; exact subset_union_left
  -- The middle polygonal piece is exactly the M-parameter subarc `[τ, τv]`.
  have hQ_eq : Q.toSet = M.toPath '' Icc τ τv := by
    have hembed : IsClosedEmbedding M.toPath :=
      M.toPath.continuous.isClosedEmbedding hinj
    have hQsub : Q.toSet ⊆ range M.toPath :=
      (hQ_subset_B.trans hB_subset_M).trans (M.toSet_eq_range_toPath ▸ Subset.rfl)
    have hQpre : IsConnected (M.toPath ⁻¹' Q.toSet) :=
      Q.isConnected_toSet.preimage_of_isClosedMap hinj hembed.isClosedMap hQsub
    have hτQ : τ ∈ M.toPath ⁻¹' Q.toSet := by simp [zu]
    have hτvQ : τv ∈ M.toPath ⁻¹' Q.toSet := by simp [zv]
    have hIcc : Icc (τ : ℝ) ↑τv ⊆ (↑) '' (M.toPath ⁻¹' Q.toSet) :=
      (hQpre.image _ continuous_subtype_val.continuousOn).Icc_subset
        (mem_image_of_mem _ hτQ) (mem_image_of_mem _ hτvQ)
    refine subset_antisymm ?_ ?_
    · intro w hwQ
      obtain ⟨t, rfl⟩ : w ∈ range M.toPath := hQsub hwQ
      have ht_ge : τ ≤ t := by
        have : M.toPath t ∈ B.toSet := hQ_subset_B hwQ
        rw [hB_eq] at this
        obtain ⟨tM, htM, htMeq⟩ := this
        exact (hinj htMeq) ▸ htM.1
      refine ⟨t, ⟨ht_ge, ?_⟩, rfl⟩
      by_contra ht
      have ht' : τv < t := lt_of_not_ge ht
      have htail : M.toPath '' Icc τv (1 : I) ⊆ (B.breakAt hzv_toSet).2.toSet := by
        have h2sub : (B.breakAt hzv_toSet).2.toSet ⊆ range M.toPath :=
          (((breakAt_toSet_union (P := B) (ha := hzv_toSet)).symm ▸ subset_union_right).trans
            hB_subset_M).trans (M.toSet_eq_range_toPath ▸ Subset.rfl)
        have h2pre : IsConnected (M.toPath ⁻¹' (B.breakAt hzv_toSet).2.toSet) :=
          (B.breakAt hzv_toSet).2.isConnected_toSet.preimage_of_isClosedMap hinj
            hembed.isClosedMap h2sub
        have hτv2 : τv ∈ M.toPath ⁻¹' (B.breakAt hzv_toSet).2.toSet := by simp [zv]
        have h12 : (1 : I) ∈ M.toPath ⁻¹' (B.breakAt hzv_toSet).2.toSet := by simp [Path.target]
        intro w hw
        obtain ⟨t', ht', rfl⟩ := hw
        obtain ⟨s, hs, hseq⟩ :=
          (h2pre.image _ continuous_subtype_val.continuousOn).Icc_subset
            (mem_image_of_mem _ hτv2) (mem_image_of_mem _ h12) ⟨ht'.1, ht'.2⟩
        exact (Subtype.ext hseq) ▸ hs
      have hinter : M.toPath t ∈ Q.toSet ∩ (B.breakAt hzv_toSet).2.toSet :=
        ⟨hwQ, htail ⟨t, ⟨ht'.le, le_top⟩, rfl⟩⟩
      rw [hQB, mem_singleton_iff] at hinter
      have ht_eq : t = τv := hinj (by simpa [zv] using hinter)
      exact ht'.ne ht_eq.symm
    · rintro w ⟨t, ht, rfl⟩
      obtain ⟨s, hs, hseq⟩ := hIcc ⟨ht.1, ht.2⟩
      exact (Subtype.ext hseq) ▸ hs
  have hQ_u : Q.toSet ∩ closedBall cu ru ⊆ {zu} := by
    intro w ⟨hwQ, hwBu⟩
    have : w ∈ (M.toPath '' Icc τ τv) ∩ closedBall cu ru := by
      rw [← hQ_eq]; exact ⟨hwQ, hwBu⟩
    simpa [hmid_u, zu] using this
  have hQ_v : Q.toSet ∩ closedBall cv rv ⊆ {zv} := by
    intro w ⟨hwQ, hwBv⟩
    have : w ∈ (M.toPath '' Icc τ τv) ∩ closedBall cv rv := by
      rw [← hQ_eq]; exact ⟨hwQ, hwBv⟩
    simpa [hmid_v, zv] using this
  have hcu_ne : cu ≠ zu := fun h ↦
    hru.ne' <| by simpa [h, dist_eq_zero, eq_comm] using hzu_dist
  have hcv_ne : zv ≠ cv := fun h ↦
    hrv.ne' <| by simpa [h, dist_eq_zero, eq_comm] using hzv_dist
  let R : PolygonalPath cu cv := ((direct cu zu).append Q).append (direct zv cv)
  have hR_toSet : R.toSet = segment ℝ cu zu ∪ Q.toSet ∪ segment ℝ zv cv := by
    simp only [R, toSet_append, toSet_direct, union_assoc]
  have hRsimple : R.IsSimple := by
    have hAQ : ((direct cu zu).append Q).IsSimple :=
      isSimple_append_iff.mpr ⟨isSimple_direct.mpr hcu_ne, hQsimple, by
        intro w hw
        have : w ∈ segment ℝ cu zu ∩ Q.toSet := by simpa only [toSet_direct] using hw
        exact hQ_u ⟨this.2, hBu hzu_dist this.1⟩⟩
    refine isSimple_append_iff.mpr ⟨hAQ, isSimple_direct.mpr hcv_ne, ?_⟩
    intro w hw
    have hw' : w ∈ (segment ℝ cu zu ∪ Q.toSet) ∩ segment ℝ zv cv := by
      simpa only [toSet_append, toSet_direct] using hw
    have hwBv : w ∈ closedBall cv rv :=
      hBv hzv_dist (segment_symm (𝕜 := ℝ) zv cv ▸ hw'.2)
    rcases hw'.1 with hwu | hwQ
    · exact (hballs.notMem_of_mem_left (hBu hzu_dist hwu) hwBv).elim
    · exact hQ_v ⟨hwQ, hwBv⟩
  refine ⟨zu, zv, R, hRsimple, hzu_dist, hzv_dist, ?_, ?_, ?_⟩
  · refine subset_antisymm ?_ ?_
    · intro w hw
      have hwR : w ∈ segment ℝ cu zu ∪ Q.toSet ∪ segment ℝ zv cv := hR_toSet ▸ hw.1
      obtain hwuQ | hwv := hwR
      · obtain hwu | hwQ := hwuQ
        · exact hwu
        · exact (mem_singleton_iff.mp (hQ_u ⟨hwQ, hw.2⟩)) ▸ right_mem_segment ℝ cu zu
      · exact (hballs.notMem_of_mem_left hw.2
          (hBv hzv_dist (segment_symm (𝕜 := ℝ) zv cv ▸ hwv))).elim
    · intro w hw
      exact ⟨hR_toSet.symm ▸ Or.inl (Or.inl hw), hBu hzu_dist hw⟩
  · refine subset_antisymm ?_ ?_
    · intro w hw
      have hwR : w ∈ segment ℝ cu zu ∪ Q.toSet ∪ segment ℝ zv cv := hR_toSet ▸ hw.1
      obtain hwuQ | hwv := hwR
      · obtain hwu | hwQ := hwuQ
        · exact (hballs.notMem_of_mem_left (hBu hzu_dist hwu) hw.2).elim
        · have hwzv : w = zv := mem_singleton_iff.mp (hQ_v ⟨hwQ, hw.2⟩)
          exact hwzv ▸ right_mem_segment ℝ cv zv
      · rwa [segment_symm]
    · intro w hw
      refine ⟨?_, hBv hzv_dist hw⟩
      rw [hR_toSet]
      exact Or.inr (segment_symm (𝕜 := ℝ) cv zv ▸ hw)
  · intro w hw
    have hwR : w ∈ segment ℝ cu zu ∪ Q.toSet ∪ segment ℝ zv cv := hR_toSet ▸ hw.1
    have hnU : w ∉ ball cu ru := fun h ↦ hw.2 (Or.inl h)
    have hnV : w ∉ ball cv rv := fun h ↦ hw.2 (Or.inr h)
    obtain hwuQ | hwv := hwR
    · obtain hwu | hwQ := hwuQ
      · have : w = zu := by
          have : w ∈ segment ℝ cu zu \ ball cu ru := ⟨hwu, hnU⟩
          rwa [segment_diff_ball_eq_singleton hru hzu_dist, mem_singleton_iff] at this
        exact hMP (this ▸ hzu_toSet)
      · exact hMP (hB_subset_M (hQ_subset_B hwQ))
    · have : w = zv := by
        have heq : segment ℝ zv cv \ ball cv rv = {zv} := by
          rw [segment_symm]
          exact segment_diff_ball_eq_singleton hrv (mdist_comm zv cv ▸ hzv_dist)
        have : w ∈ segment ℝ zv cv \ ball cv rv := ⟨hwv, hnV⟩
        rwa [heq, mem_singleton_iff] at this
      exact hMP (hB_subset_M (this ▸ hzv_toSet))


/-! ### The reduction -/

/-- Two radii of the same ball ending at distinct sphere points meet only at the centre. -/
private lemma segment_radial_inter_eq_center {c z₁ z₂ : V} {ρ : ℝ} (hρ : 0 < ρ)
    (hz₁ : Dist.dist z₁ c = ρ) (hz₂ : Dist.dist z₂ c = ρ) (hne : z₁ ≠ z₂) :
    segment ℝ c z₁ ∩ segment ℝ c z₂ = {c} := by
  refine subset_antisymm ?_ (by simp [left_mem_segment])
  intro w ⟨hw₁, hw₂⟩
  by_cases hwr : Dist.dist w c = ρ
  · have hwz₁ := eq_endpoint_of_mem_segment_of_dist_eq hρ hz₁ hw₁ hwr
    have hwz₂ := eq_endpoint_of_mem_segment_of_dist_eq hρ hz₂ hw₂ hwr
    exact (hne (hwz₁.symm.trans hwz₂)).elim
  · obtain ⟨t, ⟨ht0, _⟩, rfl⟩ := (segment_eq_image_lineMap (𝕜 := ℝ) c z₁).symm ▸ hw₁
    obtain ⟨s, ⟨hs0, _⟩, hws⟩ := (segment_eq_image_lineMap (𝕜 := ℝ) c z₂).symm ▸ hw₂
    have hts : t • (z₁ - c) = s • (z₂ - c) := by
      have := congrArg (fun z : V ↦ z - c) hws.symm
      simpa [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub, add_sub_cancel_right] using this
    by_cases ht : t = 0
    · simp [ht, AffineMap.lineMap_apply]
    · have hmul : z₁ - c = (s / t) • (z₂ - c) := by
        calc
          z₁ - c = (t⁻¹ * t) • (z₁ - c) := by rw [inv_mul_cancel₀ ht, one_smul]
          _ = t⁻¹ • (t • (z₁ - c)) := by rw [mul_smul]
          _ = t⁻¹ • (s • (z₂ - c)) := by rw [hts]
          _ = (t⁻¹ * s) • (z₂ - c) := by rw [smul_smul]
          _ = (s / t) • (z₂ - c) := by rw [div_eq_mul_inv, mul_comm]
      have habs : |s / t| = 1 := by
        have hz₁' : ‖z₁ - c‖ = ρ := by simpa [Dist.dist, dist_eq_norm] using hz₁
        have hz₂' : ‖z₂ - c‖ = ρ := by simpa [Dist.dist, dist_eq_norm] using hz₂
        have : ‖z₁ - c‖ = |s / t| * ‖z₂ - c‖ := by
          rw [hmul, norm_smul, Real.norm_eq_abs]
        rwa [hz₁', hz₂', eq_comm, mul_eq_right₀ hρ.ne'] at this
      have hst : s / t = 1 := by
        have hnonneg : 0 ≤ s / t := div_nonneg hs0 ht0
        rwa [abs_of_nonneg hnonneg] at habs
      have : z₁ = z₂ := sub_left_inj.mp (by rwa [hst, one_smul] at hmul)
      exact (hne this).elim

/-- Status.md 2.6: a drawing of a finite loopless graph in a real normed space can be replaced by a
polygonal drawing with the same vertex positions. -/
theorem Drawing.exists_plDrawing [G.Finite] [G.Loopless] (D : Drawing G V) :
    ∃ Q : PLDrawing G V, ∀ x, Q.toDrawing.vertex x = D.vertex x := by
  classical
  obtain ⟨r, hpos, hdisj, hball⟩ := D.exists_vertexRadius
  obtain ⟨a, b, Mid, _hMid_sub, hdist_a, hdist_b, _hmeet_a, _hmeet_b, havoid, hMid_disj⟩ :=
    D.exists_middlePaths hpos hdisj hball
  have hsrc_ne_tgt (e : E(G)) : edgeSource e ≠ edgeTarget e := by
    intro heq
    exact (isLink_edgeSource_edgeTarget e).ne (congrArg Subtype.val heq)
  -- Closed obstacle sets: balls at vertices that are not ends of `e`.
  let K : E(G) → Set V := fun e ↦
    ⋃ x ∈ {x : V(G) | x ≠ edgeSource e ∧ x ≠ edgeTarget e}, closedBall (D.vertex x) (r x)
  have hK_closed (e : E(G)) : IsClosed (K e) :=
    (toFinite _).isClosed_biUnion fun _ _ ↦ isClosed_closedBall
  have hMid_K (e : E(G)) : Disjoint (range (Mid e)) (K e) := by
    refine disjoint_left.mpr ?_
    intro z hzMid hzK
    obtain ⟨x, hx, hzB⟩ := mem_iUnion₂.mp hzK
    exact (havoid e x hx.1 hx.2).notMem_of_mem_left hzMid hzB
  obtain ⟨Ppoly, hP_disj, hP_K⟩ :=
    exists_polygonalPath_family_of_disjoint Mid hMid_disj K hK_closed hMid_K
  have ha_mem (e : E(G)) :
      a e ∈ closedBall (D.vertex (edgeSource e)) (r (edgeSource e)) :=
    mem_closedBall.mpr (le_of_eq (hdist_a e))
  have hb_mem (e : E(G)) :
      b e ∈ closedBall (D.vertex (edgeTarget e)) (r (edgeTarget e)) :=
    mem_closedBall.mpr (le_of_eq (hdist_b e))
  choose zu zv cell hcell using fun e : E(G) ↦
    exists_isSimple_radial (hpos _) (hpos _) (hdisj (hsrc_ne_tgt e))
      (Ppoly e) (ha_mem e) (hb_mem e)
  have hcell_simple (e : E(G)) : (cell e).IsSimple := (hcell e).1
  have hzu_dist (e : E(G)) :
      Dist.dist (zu e) (D.vertex (edgeSource e)) = r (edgeSource e) := (hcell e).2.1
  have hzv_dist (e : E(G)) :
      Dist.dist (zv e) (D.vertex (edgeTarget e)) = r (edgeTarget e) := (hcell e).2.2.1
  have hcell_src (e : E(G)) :
      (cell e).toSet ∩ closedBall (D.vertex (edgeSource e)) (r (edgeSource e)) =
        segment ℝ (D.vertex (edgeSource e)) (zu e) := (hcell e).2.2.2.1
  have hcell_tgt (e : E(G)) :
      (cell e).toSet ∩ closedBall (D.vertex (edgeTarget e)) (r (edgeTarget e)) =
        segment ℝ (D.vertex (edgeTarget e)) (zv e) := (hcell e).2.2.2.2.1
  have hcell_mid (e : E(G)) :
      (cell e).toSet \
          (ball (D.vertex (edgeSource e)) (r (edgeSource e)) ∪
            ball (D.vertex (edgeTarget e)) (r (edgeTarget e))) ⊆
        (Ppoly e).toSet := (hcell e).2.2.2.2.2
  have hzu_mem_P (e : E(G)) : zu e ∈ (Ppoly e).toSet := by
    have hzu_cell : zu e ∈ (cell e).toSet := by
      have : zu e ∈
          (cell e).toSet ∩ closedBall (D.vertex (edgeSource e)) (r (edgeSource e)) := by
        rw [hcell_src]; exact right_mem_segment ℝ _ _
      exact this.1
    refine hcell_mid e ⟨hzu_cell, ?_⟩
    rintro (hu | hv)
    · exact (lt_self_iff_false _).mp <| (mem_ball.mp hu).trans_eq (hzu_dist e).symm
    · exact (hdisj (hsrc_ne_tgt e)).notMem_of_mem_left
        (mem_closedBall.mpr (le_of_eq (hzu_dist e)))
        (mem_closedBall.mpr (le_of_lt (mem_ball.mp hv)))
  have hzv_mem_P (e : E(G)) : zv e ∈ (Ppoly e).toSet := by
    have hzv_cell : zv e ∈ (cell e).toSet := by
      have : zv e ∈
          (cell e).toSet ∩ closedBall (D.vertex (edgeTarget e)) (r (edgeTarget e)) := by
        rw [hcell_tgt]; exact right_mem_segment ℝ _ _
      exact this.1
    refine hcell_mid e ⟨hzv_cell, ?_⟩
    rintro (hu | hv)
    · exact (hdisj (hsrc_ne_tgt e)).notMem_of_mem_left
        (mem_closedBall.mpr (le_of_lt (mem_ball.mp hu)))
        (mem_closedBall.mpr (le_of_eq (hzv_dist e)))
    · exact (lt_self_iff_false _).mp <| (mem_ball.mp hv).trans_eq (hzv_dist e).symm
  have hcell_avoid (e : E(G)) (x : V(G)) (hxu : x ≠ edgeSource e) (hxv : x ≠ edgeTarget e) :
      Disjoint (cell e).toSet (closedBall (D.vertex x) (r x)) := by
    refine disjoint_left.mpr ?_
    intro w hwcell hwB
    by_cases hwu : w ∈ closedBall (D.vertex (edgeSource e)) (r (edgeSource e))
    · exact (hdisj hxu.symm).notMem_of_mem_left hwu hwB
    · by_cases hwv : w ∈ closedBall (D.vertex (edgeTarget e)) (r (edgeTarget e))
      · exact (hdisj hxv.symm).notMem_of_mem_left hwv hwB
      · have hwP : w ∈ (Ppoly e).toSet :=
          hcell_mid e ⟨hwcell, by
            rintro (hu | hv)
            · exact hwu (mem_closedBall.mpr (le_of_lt (mem_ball.mp hu)))
            · exact hwv (mem_closedBall.mpr (le_of_lt (mem_ball.mp hv)))⟩
        exact (hP_K e).notMem_of_mem_left hwP <|
          mem_iUnion₂.mpr ⟨x, ⟨hxu, hxv⟩, hwB⟩
  have hlen (e : E(G)) : 0 < (cell e).length :=
    length_pos_of_ne (cell e) (D.vertex_injective.ne (hsrc_ne_tgt e))
  have hsimple (e : E(G)) : (cell e).IsSimpleArcOrLoop :=
    (hcell_simple e).isSimpleArcOrLoop (hlen e)
  have hcv (e : E(G)) : Disjoint
      ((cell e).toSet \
        {D.vertex (edgeSource e), D.vertex (edgeTarget e)}) (range D.vertex) := by
    refine disjoint_left.mpr ?_
    rintro w ⟨hwcell, hwne⟩ ⟨x, rfl⟩
    have hxne : x ≠ edgeSource e ∧ x ≠ edgeTarget e := by
      constructor
      · intro h; exact hwne (by simp [h])
      · intro h; exact hwne (by simp [h])
    exact (hcell_avoid e x hxne.1 hxne.2).notMem_of_mem_left hwcell <|
      mem_closedBall_self (hpos x).le
  have hcc (e f : E(G)) (hef : e ≠ f) : Disjoint
      ((cell e).toSet \ {D.vertex (edgeSource e), D.vertex (edgeTarget e)})
      ((cell f).toSet \ {D.vertex (edgeSource f), D.vertex (edgeTarget f)}) := by
    refine disjoint_left.mpr ?_
    intro w ⟨hwe, hwe_ne⟩ ⟨hwf, _hwf_ne⟩
    by_cases hwe_u : w ∈ closedBall (D.vertex (edgeSource e)) (r (edgeSource e))
    · have hwseg : w ∈ segment ℝ (D.vertex (edgeSource e)) (zu e) := by
        have : w ∈
            (cell e).toSet ∩ closedBall (D.vertex (edgeSource e)) (r (edgeSource e)) :=
          ⟨hwe, hwe_u⟩
        rwa [hcell_src] at this
      have hwne_u : w ≠ D.vertex (edgeSource e) := fun h ↦ hwe_ne (by simp [h])
      by_cases h_share_u : edgeSource e = edgeSource f ∨ edgeSource e = edgeTarget f
      · rcases h_share_u with huf | hvf
        · have hzne : zu e ≠ zu f := fun hz ↦
            (hP_disj hef).notMem_of_mem_left (hzu_mem_P e) (hz ▸ hzu_mem_P f)
          have hwf_u : w ∈ closedBall (D.vertex (edgeSource f)) (r (edgeSource f)) := by
            simpa [huf] using hwe_u
          have hwsegf : w ∈ segment ℝ (D.vertex (edgeSource f)) (zu f) := by
            have : w ∈
                (cell f).toSet ∩ closedBall (D.vertex (edgeSource f)) (r (edgeSource f)) :=
              ⟨hwf, hwf_u⟩
            rwa [hcell_src] at this
          have hinter : w ∈ ({D.vertex (edgeSource e)} : Set V) := by
            rw [← segment_radial_inter_eq_center (hpos _) (hzu_dist e)
              (by simpa [huf] using hzu_dist f) hzne]
            exact ⟨hwseg, by simpa [huf] using hwsegf⟩
          exact hwne_u (mem_singleton_iff.mp hinter)
        · have hzne : zu e ≠ zv f := fun hz ↦
            (hP_disj hef).notMem_of_mem_left (hzu_mem_P e) (hz ▸ hzv_mem_P f)
          have hwf_v : w ∈ closedBall (D.vertex (edgeTarget f)) (r (edgeTarget f)) := by
            simpa [hvf] using hwe_u
          have hwsegf : w ∈ segment ℝ (D.vertex (edgeTarget f)) (zv f) := by
            have : w ∈
                (cell f).toSet ∩ closedBall (D.vertex (edgeTarget f)) (r (edgeTarget f)) :=
              ⟨hwf, hwf_v⟩
            rwa [hcell_tgt] at this
          have hinter : w ∈ ({D.vertex (edgeSource e)} : Set V) := by
            rw [← segment_radial_inter_eq_center (hpos _) (hzu_dist e)
              (by simpa [hvf] using hzv_dist f) hzne]
            exact ⟨hwseg, by simpa [hvf] using hwsegf⟩
          exact hwne_u (mem_singleton_iff.mp hinter)
      · push Not at h_share_u
        exact (hcell_avoid f (edgeSource e) h_share_u.1 h_share_u.2).notMem_of_mem_left
          hwf hwe_u
    · by_cases hwe_v : w ∈ closedBall (D.vertex (edgeTarget e)) (r (edgeTarget e))
      · have hwseg : w ∈ segment ℝ (D.vertex (edgeTarget e)) (zv e) := by
          have : w ∈
              (cell e).toSet ∩ closedBall (D.vertex (edgeTarget e)) (r (edgeTarget e)) :=
            ⟨hwe, hwe_v⟩
          rwa [hcell_tgt] at this
        have hwne_v : w ≠ D.vertex (edgeTarget e) := fun h ↦ hwe_ne (by simp [h])
        by_cases h_share_v : edgeTarget e = edgeSource f ∨ edgeTarget e = edgeTarget f
        · rcases h_share_v with huf | hvf
          · have hzne : zv e ≠ zu f := fun hz ↦
              (hP_disj hef).notMem_of_mem_left (hzv_mem_P e) (hz ▸ hzu_mem_P f)
            have hwf_u : w ∈ closedBall (D.vertex (edgeSource f)) (r (edgeSource f)) := by
              simpa [huf] using hwe_v
            have hwsegf : w ∈ segment ℝ (D.vertex (edgeSource f)) (zu f) := by
              have : w ∈
                  (cell f).toSet ∩ closedBall (D.vertex (edgeSource f)) (r (edgeSource f)) :=
                ⟨hwf, hwf_u⟩
              rwa [hcell_src] at this
            have hinter : w ∈ ({D.vertex (edgeTarget e)} : Set V) := by
              rw [← segment_radial_inter_eq_center (hpos _) (hzv_dist e)
                (by simpa [huf] using hzu_dist f) hzne]
              exact ⟨hwseg, by simpa [huf] using hwsegf⟩
            exact hwne_v (mem_singleton_iff.mp hinter)
          · have hzne : zv e ≠ zv f := fun hz ↦
              (hP_disj hef).notMem_of_mem_left (hzv_mem_P e) (hz ▸ hzv_mem_P f)
            have hwf_v : w ∈ closedBall (D.vertex (edgeTarget f)) (r (edgeTarget f)) := by
              simpa [hvf] using hwe_v
            have hwsegf : w ∈ segment ℝ (D.vertex (edgeTarget f)) (zv f) := by
              have : w ∈
                  (cell f).toSet ∩ closedBall (D.vertex (edgeTarget f)) (r (edgeTarget f)) :=
                ⟨hwf, hwf_v⟩
              rwa [hcell_tgt] at this
            have hinter : w ∈ ({D.vertex (edgeTarget e)} : Set V) := by
              rw [← segment_radial_inter_eq_center (hpos _) (hzv_dist e)
                (by simpa [hvf] using hzv_dist f) hzne]
              exact ⟨hwseg, by simpa [hvf] using hwsegf⟩
            exact hwne_v (mem_singleton_iff.mp hinter)
        · push Not at h_share_v
          exact (hcell_avoid f (edgeTarget e) h_share_v.1 h_share_v.2).notMem_of_mem_left
            hwf hwe_v
      · have hwP : w ∈ (Ppoly e).toSet :=
          hcell_mid e ⟨hwe, by
            rintro (hu | hv)
            · exact hwe_u (mem_closedBall.mpr (le_of_lt (mem_ball.mp hu)))
            · exact hwe_v (mem_closedBall.mpr (le_of_lt (mem_ball.mp hv)))⟩
        by_cases hwf_u : w ∈ closedBall (D.vertex (edgeSource f)) (r (edgeSource f))
        · by_cases h_share : edgeSource f = edgeSource e ∨ edgeSource f = edgeTarget e
          · rcases h_share with h | h
            · exact hwe_u (by simpa [h] using hwf_u)
            · exact hwe_v (by simpa [h] using hwf_u)
          · push Not at h_share
            exact (hP_K e).notMem_of_mem_left hwP <|
              mem_iUnion₂.mpr ⟨edgeSource f, ⟨h_share.1, h_share.2⟩, hwf_u⟩
        · by_cases hwf_v : w ∈ closedBall (D.vertex (edgeTarget f)) (r (edgeTarget f))
          · by_cases h_share : edgeTarget f = edgeSource e ∨ edgeTarget f = edgeTarget e
            · rcases h_share with h | h
              · exact hwe_u (by simpa [h] using hwf_v)
              · exact hwe_v (by simpa [h] using hwf_v)
            · push Not at h_share
              exact (hP_K e).notMem_of_mem_left hwP <|
                mem_iUnion₂.mpr ⟨edgeTarget f, ⟨h_share.1, h_share.2⟩, hwf_v⟩
          · have hwPf : w ∈ (Ppoly f).toSet :=
              hcell_mid f ⟨hwf, by
                rintro (hu | hv)
                · exact hwf_u (mem_closedBall.mpr (le_of_lt (mem_ball.mp hu)))
                · exact hwf_v (mem_closedBall.mpr (le_of_lt (mem_ball.mp hv)))⟩
            exact (hP_disj hef).notMem_of_mem_left hwP hwPf
  refine ⟨PLDrawing.ofCells D.vertex D.vertex_injective cell hsimple hcv hcc, ?_⟩
  intro x
  exact PLDrawing.ofCells_vertex x

/-- Status.md 2.6 in the plane. -/
theorem Planar.plPlanar [G.Finite] [G.Loopless] (hG : G.Planar) : G.PLPlanar :=
  ⟨hG.some.exists_plDrawing.choose⟩

/-- Status.md 2.7. -/
theorem planar_iff_plPlanar [G.Finite] [G.Loopless] : G.Planar ↔ G.PLPlanar :=
  ⟨Planar.plPlanar, PLPlanar.planar⟩

end

end Graph
