import Matroid.Graph.Planarity.PLDrawing
import Matroid.Graph.Planarity.Face
import Matroid.ForMathlib.Geometry.DiskMinusRadii
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

/- **Proof route for `exists_radius`** (formalisation helper). Status.md 3.6's proof is complete and
correct; what follows is only which Lean declarations carry it, all checked against this pin.

*Prerequisite.* `PLDrawing.exists_finite_support` (`PLDrawing.lean:127`, proved). Everything below
assumes the support is `range vertex ∪ ⋃ s ∈ S, segment ℝ s.1 s.2` for a finite `S`.

*The radius.* Split `S` into the segments whose closure contains `p` and the rest. The rest has
compact union — `isCompact_segment` in `Matroid/ForMathlib/Analysis/Convex/Segment.lean`, then
`Set.Finite.isCompact_biUnion` — and does not contain `p`, so
`IsClosed.notMem_iff_infDist_pos` (`Mathlib/Topology/MetricSpace/HausdorffDistance.lean`, and
`infDist_pos_iff_notMem_closure` at `:692`) gives a positive lower bound. Take `ρ` below that, below
`dist p s.1` and `dist p s.2` for each remaining segment, and below `Finset.min'` of the finitely
many such numbers. `Y` is then the set of points where those segments cross `sphere p ρ`.

*The expensive half.* The `⊇` direction of the stated equality — that every segment germ at `p` is
captured and nothing else intrudes — is the whole cost; the `⊆` direction follows from the radius
choice. Distinctness of the `y_i` is `D.toDrawing.injective`.

*The two corollaries* (`exists_radius_vertex`, `exists_radius_edgeInterior`) are separate
obligations on top: the degree count `(Y.card : ℕ∞) = G.degree v.1` needs a bijection between `Y`
and the edge-ends at `v`, with a loop supplying two, and is not implied by `exists_radius`.

Nothing in this block needs the plane; the statement is over a real normed space deliberately
(Kuratowski `Decisions.md` D11). Only the *count* of complementary pieces is two-dimensional. -/

/- Dropped `Y.Nonempty`: Status.md's `d ≥ 1` conflicts with `d = deg v` at isolated vertices;
the star there is `{p}` with `Y = ∅`, so the equality uses `{p} ∪ ⋃ …`. -/


/-- A point off a closed set stays a fixed positive distance from all of it. The bound is stated
pointwise rather than as `infDist p K`, which is what lets the empty case go without its own
branch: `infDist p ∅ = 0`, but `∀ x ∈ ∅, _` is vacuous. -/
private lemma exists_pos_le_dist_of_notMem {K : Set V} (hK : IsClosed K) {p : V} (hp : p ∉ K) :
    ∃ δ > 0, ∀ x ∈ K, δ ≤ dist p x := by
  obtain rfl | hne := K.eq_empty_or_nonempty
  · exact ⟨1, one_pos, by simp⟩
  exact ⟨infDist p K, (hK.notMem_iff_infDist_pos hne).mp hp, fun _ hx ↦ infDist_le_dist_of_mem hx⟩

/-- **The star lemma.** About each of its points, a polygonal drawing of a finite graph meets a
small enough closed ball in a union of straight radii, one for each direction in which the drawing
leaves the point.

No hypothesis on the ambient space beyond a norm: the radius is chosen below the distance from `p`
to the finitely many segments not touching it, below the length of each segment ending at `p`, and
below the distance to the endpoints of a segment through `p`. -/
theorem exists_radius [G.Finite] (D : PLDrawing G V) {p : V} (hp : p ∈ D.toDrawing.support) :
    ∃ ρ > 0, ∃ Y : Finset V, ↑Y ⊆ sphere p ρ ∧
      closedBall p ρ ∩ D.toDrawing.support = {p} ∪ ⋃ y ∈ Y, segment ℝ p y := by
  classical
  obtain ⟨S0, hSfin, hsupp⟩ := D.exists_finite_support
  let Sp : Set (V × V) := {s ∈ S0 | p ∈ segment ℝ s.1 s.2}
  let Srest : Set (V × V) := {s ∈ S0 | p ∉ segment ℝ s.1 s.2}
  have hSpfin : Sp.Finite := hSfin.subset fun _ h ↦ h.1
  have hSrestfin : Srest.Finite := hSfin.subset fun _ h ↦ h.1
  let K : Set V := (range D.toDrawing.vertex \ {p}) ∪ ⋃ s ∈ Srest, segment ℝ s.1 s.2
  have hKcompact : IsCompact K :=
    (((Set.finite_range D.toDrawing.vertex).subset sdiff_subset).isCompact).union
      (hSrestfin.isCompact_biUnion fun _ _ ↦ isCompact_segment _ _)
  have hKclosed : IsClosed K := hKcompact.isClosed
  have hpK : p ∉ K := by
    refine not_or.mpr ⟨fun h ↦ h.2 rfl, ?_⟩
    intro hp'
    obtain ⟨s, hs, hseg⟩ := mem_iUnion₂.mp hp'
    exact hs.2 hseg
  obtain ⟨δ, hδpos, hδle⟩ := exists_pos_le_dist_of_notMem hKclosed hpK
  -- Everything below is a statement about an *endpoint* of a segment through `p`, and never about
  -- which of the two endpoints it is. Ranging over endpoints rather than over pairs is what
  -- removes the `s.1`/`s.2` duplication from the four facts that follow.
  let ends : Finset V := hSpfin.toFinset.biUnion fun s ↦ ({s.1, s.2} : Finset V).erase p
  have hends_ne : ∀ z ∈ ends, z ≠ p := by
    intro z hz
    obtain ⟨s, -, hz⟩ := Finset.mem_biUnion.mp hz
    exact Finset.ne_of_mem_erase hz
  have hends_seg : ∀ z ∈ ends, ∃ s ∈ Sp, segment ℝ p z ⊆ segment ℝ s.1 s.2 := by
    intro z hz
    obtain ⟨s, hsF, hz⟩ := Finset.mem_biUnion.mp hz
    have hs := hSpfin.mem_toFinset.mp hsF
    have hsplit := segment_union_eq_segment hs.2
    have hz' := Finset.mem_of_mem_erase hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz'
    refine ⟨s, hs, ?_⟩
    obtain rfl | rfl := hz'
    · rw [← hsplit, segment_symm]
      exact subset_union_left
    rw [← hsplit]
    exact subset_union_right
  have hmem_ends : ∀ s ∈ Sp, ∀ z, z = s.1 ∨ z = s.2 → z ≠ p → z ∈ ends := fun s hs z hz hzp ↦
    Finset.mem_biUnion.mpr
      ⟨s, hSpfin.mem_toFinset.mpr hs, Finset.mem_erase.mpr ⟨hzp, by simpa using hz⟩⟩
  let dists : Finset ℝ := ends.image (dist p ·)
  have hdists_pos : ∀ d ∈ dists, 0 < d := by
    intro d hd
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hd
    exact dist_pos.mpr (hends_ne z hz).symm
  let bounds : Finset ℝ := insert δ (insert (1 : ℝ) dists)
  have hbounds_ne : bounds.Nonempty := Finset.insert_nonempty _ _
  let ρ : ℝ := bounds.min' hbounds_ne / 2
  have hρpos : 0 < ρ := half_pos <| by
    have hxpos : ∀ x ∈ bounds, 0 < x := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hδpos
      · rcases Finset.mem_insert.mp hx with rfl | hx
        · norm_num
        · exact hdists_pos x hx
    exact hxpos _ (Finset.min'_mem _ _)
  have hρ_lt_δ : ρ < δ :=
    calc
      ρ = bounds.min' hbounds_ne / 2 := rfl
      _ ≤ δ / 2 :=
        div_le_div_of_nonneg_right (Finset.min'_le _ _ (Finset.mem_insert_self _ _)) (by norm_num)
      _ < δ := half_lt_self hδpos
  have hρ_le_end : ∀ z ∈ ends, ρ ≤ dist p z := by
    intro z hz
    have hle : bounds.min' hbounds_ne ≤ dist p z :=
      Finset.min'_le _ _ (Finset.mem_insert_of_mem
        (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hz)))
    exact (div_le_div_of_nonneg_right hle (by norm_num)).trans (half_le_self dist_nonneg)
  have hnotK {x : V} (hxball : x ∈ closedBall p ρ) (hxK : x ∈ K) : False := by
    have hle := hδle x hxK
    rw [PseudoMetricSpace.dist_comm] at hle
    linarith [mem_closedBall.mp hxball, hρ_lt_δ]
  let Y : Finset V := ends.image (radialPoint p · ρ)
  have hYsphere : ↑Y ⊆ sphere p ρ := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp (show y ∈ Y from hy)
    exact mem_sphere_radialPoint p z hρpos.le (hends_ne z hz)
  refine ⟨ρ, hρpos, Y, hYsphere, subset_antisymm ?_ ?_⟩
  · intro x ⟨hxball, hxsup⟩
    rw [hsupp] at hxsup
    rcases hxsup with hxV | hxS
    · rcases eq_or_ne x p with rfl | hxp
      · exact Or.inl rfl
      · exact (hnotK hxball (Or.inl ⟨hxV, hxp⟩)).elim
    · obtain ⟨s, hsS0, hxseg⟩ := mem_iUnion₂.mp hxS
      by_cases hpseg : p ∈ segment ℝ s.1 s.2
      · have hsSp : s ∈ Sp := ⟨hsS0, hpseg⟩
        -- One argument for either endpoint, applied twice below.
        have hcap : ∀ z, z = s.1 ∨ z = s.2 → z ≠ p → x ∈ segment ℝ p z →
            x ∈ ({p} : Set V) ∪ ⋃ y ∈ Y, segment ℝ p y := by
          intro z hz hzp hxz
          have hzend := hmem_ends s hsSp z hz hzp
          have hxrad : x ∈ segment ℝ p (radialPoint p z ρ) := by
            have hx' : x ∈ closedBall p ρ ∩ segment ℝ p z := ⟨hxball, hxz⟩
            rwa [segment_inter_closedBall_eq_radial p z hρpos hzp (hρ_le_end z hzend)] at hx'
          exact Or.inr
            (mem_iUnion₂.mpr ⟨radialPoint p z ρ, Finset.mem_image_of_mem _ hzend, hxrad⟩)
        have hx' : x ∈ segment ℝ s.1 p ∪ segment ℝ p s.2 :=
          (segment_union_eq_segment hpseg).symm ▸ hxseg
        obtain hx1 | hx2 := hx'
        · rw [segment_symm] at hx1
          obtain heq | hne := eq_or_ne s.1 p
          · subst heq
            exact Or.inl (by simpa [segment_same] using hx1)
          exact hcap s.1 (Or.inl rfl) hne hx1
        obtain heq | hne := eq_or_ne s.2 p
        · subst heq
          exact Or.inl (by simpa [segment_same] using hx2)
        exact hcap s.2 (Or.inr rfl) hne hx2
      exact (hnotK hxball (Or.inr (mem_iUnion₂.mpr ⟨s, ⟨hsS0, hpseg⟩, hxseg⟩))).elim
  · intro x hx
    obtain rfl | hx := hx
    · exact ⟨mem_closedBall_self hρpos.le, hp⟩
    obtain ⟨y, hyY, hxseg⟩ := mem_iUnion₂.mp hx
    have hyball : y ∈ closedBall p ρ := sphere_subset_closedBall (hYsphere hyY)
    refine ⟨(convex_closedBall p ρ).segment_subset (mem_closedBall_self hρpos.le) hyball hxseg, ?_⟩
    obtain ⟨z, hzend, rfl⟩ := Finset.mem_image.mp hyY
    obtain ⟨s, hsSp, hsub⟩ := hends_seg z hzend
    have h1 : segment ℝ p (radialPoint p z ρ) ⊆ segment ℝ p z :=
      (convex_segment p z).segment_subset (left_mem_segment _ _ _)
        (radialPoint_mem_segment p z hρpos.le (hρ_le_end z hzend))
    rw [hsupp]
    exact Or.inr (mem_iUnion₂.mpr ⟨s, hsSp.1, hsub (h1 hxseg)⟩)

private lemma pathInterior_subset_range {x y : V} (P : Path x y) :
    Drawing.pathInterior P ⊆ range P := by
  rintro _ ⟨t, ht, rfl⟩
  exact ⟨t, rfl⟩


private lemma exists_edge_ending_at_last {x y : V} {P : PolygonalPath x y} (h : 0 < P.length) :
    ∃ a, (a, y) ∈ P.edges := by
  have hrev : 0 < P.reverse.length := by simpa using h
  cases hP : P.reverse with
  | nil => simp [hP] at hrev
  | cons _ a Q =>
    refine ⟨a, ?_⟩
    have : (y, a) ∈ P.reverse.edges := by simp [hP]
    simpa [PolygonalPath.reverse_edges] using this

private lemma exists_edge_starting_at_first {x y : V} {P : PolygonalPath x y} (h : 0 < P.length) :
    ∃ b, (x, b) ∈ P.edges := by
  cases P with
  | nil => simp at h
  | cons _ b Q => exact ⟨b, by simp⟩

private lemma isSimple_left_of_append_isSimpleArcOrLoop {x p y : V}
    {A : PolygonalPath x p} {B : PolygonalPath p y}
    (h : (A.append B).IsSimpleArcOrLoop) (hxp : x ≠ p) : A.IsSimple := by
  rcases h with ⟨hS, _⟩ | ⟨heq, hL⟩
  · exact hS.of_append_left
  · subst y
    rw [PolygonalPath.cast_rfl] at hL
    exact PolygonalPath.IsSimpleLoop.isSimple_of_append_left hxp hL

private lemma isSimple_right_of_append_isSimpleArcOrLoop {x p y : V}
    {A : PolygonalPath x p} {B : PolygonalPath p y}
    (h : (A.append B).IsSimpleArcOrLoop) (hxp : x ≠ p) : B.IsSimple := by
  rcases h with ⟨hS, _⟩ | ⟨heq, hL⟩
  · exact hS.of_append_right
  · subst y
    rw [PolygonalPath.cast_rfl] at hL
    exact (PolygonalPath.isSimpleLoop_append_iff hxp).mp hL |>.2.1

private lemma toSet_inter_subset_of_append_isSimpleArcOrLoop {x p y : V}
    {A : PolygonalPath x p} {B : PolygonalPath p y}
    (h : (A.append B).IsSimpleArcOrLoop) (hxp : x ≠ p) :
    A.toSet ∩ B.toSet ⊆ ({x, p} : Set V) := by
  rcases h with ⟨hS, _⟩ | ⟨heq, hL⟩
  · intro u hu
    exact Or.inr ((PolygonalPath.isSimple_append_iff.mp hS).2.2 hu)
  · subst y
    rw [PolygonalPath.cast_rfl] at hL
    exact ((PolygonalPath.isSimpleLoop_append_iff hxp).mp hL).2.2.le


private lemma append_cast_right {x p y : V} (A : PolygonalPath x p) (B : PolygonalPath p y)
    (heq : y = x) :
    (A.append B).cast rfl heq = A.append (B.cast rfl heq) := by
  induction heq
  rfl

private lemma eq_last_edge_of_mem_segment {x p : V} {A : PolygonalPath x p} (hA : A.IsSimple)
    {a : V} (ha : (a, p) ∈ A.edges) {s : V × V} (hs : s ∈ A.edges)
    (hps : p ∈ segment ℝ s.1 s.2) : s = (a, p) := by
  have hAr : A.reverse.IsSimple := PolygonalPath.isSimple_reverse.mpr hA
  have ha' : (p, a) ∈ A.reverse.edges := by simpa [PolygonalPath.reverse_edges] using ha
  have hs' : (s.2, s.1) ∈ A.reverse.edges := by simpa [PolygonalPath.reverse_edges] using hs
  have hps' : p ∈ segment ℝ s.2 s.1 := by rwa [segment_symm]
  cases hArev : A.reverse with
  | nil =>
    have hlen : A.reverse.length = 0 := by rw [hArev]; rfl
    have : A.length = 0 := by simpa using hlen
    cases A with
    | nil => simp at ha
    | cons => simp at this
  | cons _ b Q =>
    have hAr' : (PolygonalPath.cons p b Q).IsSimple := hArev ▸ hAr
    obtain ⟨hpb, hQ, hmeet⟩ := PolygonalPath.isSimple_cons_iff.mp hAr'
    have ha_mem : (p, a) ∈ (p, b) :: Q.edges := by
      simpa [hArev, PolygonalPath.edges_cons] using ha'
    have hb_eq : a = b := by
      rcases List.mem_cons.mp ha_mem with heq | haQ
      · exact (Prod.mk.inj heq).2
      · exact ((List.nodup_cons.mp hAr'.1).1 (Q.fst_mem_vertices haQ)).elim
    subst b
    have hs_mem : (s.2, s.1) ∈ (p, a) :: Q.edges := by
      simpa [hArev, PolygonalPath.edges_cons] using hs'
    rcases List.mem_cons.mp hs_mem with heq | hsQ
    · obtain ⟨hs2, hs1⟩ := Prod.mk.inj heq
      exact Prod.ext hs1 hs2
    · have hpQ : p ∈ Q.toSet := Q.segment_subset_toSet hsQ hps'
      have : p = a := mem_singleton_iff.mp (hmeet ⟨left_mem_segment ℝ p a, hpQ⟩)
      exact (hpb this).elim

private lemma eq_first_edge_of_mem_segment {p y : V} {B : PolygonalPath p y} (hB : B.IsSimple)
    {b : V} (hb : (p, b) ∈ B.edges) {s : V × V} (hs : s ∈ B.edges)
    (hps : p ∈ segment ℝ s.1 s.2) : s = (p, b) := by
  cases hBcases : B with
  | nil => simp [hBcases] at hb
  | cons _ c Q =>
    have hBsimp : (PolygonalPath.cons p c Q).IsSimple := hBcases ▸ hB
    obtain ⟨hpc, hQ, hmeet⟩ := PolygonalPath.isSimple_cons_iff.mp hBsimp
    have hb_mem : (p, b) ∈ (p, c) :: Q.edges := by
      simpa [hBcases, PolygonalPath.edges_cons] using hb
    have hc_eq : b = c := by
      rcases List.mem_cons.mp hb_mem with heq | hbQ
      · exact (Prod.mk.inj heq).2
      · exact ((List.nodup_cons.mp hBsimp.1).1 (Q.fst_mem_vertices hbQ)).elim
    subst c
    have hs_mem : s ∈ (p, b) :: Q.edges := by
      simpa [hBcases, PolygonalPath.edges_cons] using hs
    rcases List.mem_cons.mp hs_mem with heq | hsQ
    · exact heq
    · have hpQ : p ∈ Q.toSet := Q.segment_subset_toSet hsQ hps
      have : p = b := mem_singleton_iff.mp (hmeet ⟨left_mem_segment ℝ p b, hpQ⟩)
      exact (hpc this).elim

/-- At a point interior to one cell there are exactly two radii, and both lie along that cell. -/
theorem exists_radius_edgeInterior [G.Finite] (D : PLDrawing G V) {e : E(G)} {p : V}
    (hp : p ∈ Drawing.pathInterior (D.toDrawing.edgePath e)) :
    ∃ ρ > 0, ∃ Y : Finset V, ↑Y ⊆ sphere p ρ ∧ Y.card = 2 ∧
      ↑Y ⊆ range (D.toDrawing.edgePath e) ∧
      closedBall p ρ ∩ D.toDrawing.support =
        {p} ∪ ⋃ y ∈ Y, segment ℝ p y := by
  classical
  have hp_range : p ∈ range (D.toDrawing.edgePath e) := pathInterior_subset_range _ hp
  have hp_cell : p ∈ (D.cell e).toSet := by rwa [← D.range_edgePath e]
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
    obtain ⟨a, haA⟩ := exists_edge_ending_at_last hApos
    obtain ⟨b, hbB⟩ := exists_edge_starting_at_first hBpos
    have ha : (a, p) ∈ (D.cell e).edges := by
      simpa [hAB, PolygonalPath.append_edges] using Or.inl haA
    have hb : (p, b) ∈ (D.cell e).edges := by
      simpa [hAB, PolygonalPath.append_edges] using Or.inr hbB
    have hxp : D.toDrawing.vertex (edgeSource e) ≠ p := hpx.symm
    have hA : A.IsSimple :=
      isSimple_left_of_append_isSimpleArcOrLoop (hAB ▸ D.cell_isSimpleArcOrLoop e) hxp
    have hB : B.IsSimple :=
      isSimple_right_of_append_isSimpleArcOrLoop (hAB ▸ D.cell_isSimpleArcOrLoop e) hxp
    have hne_a : a ≠ p := hA.hasNondegenerateEdges _ haA
    have hne_b : b ≠ p := (hB.hasNondegenerateEdges _ hbB).symm
    have honly : ∀ s ∈ (D.cell e).edges, p ∈ segment ℝ s.1 s.2 → s = (a, p) ∨ s = (p, b) := by
      intro s hs hps
      have hs' : s ∈ A.edges ∨ s ∈ B.edges := by
        simpa [hAB, PolygonalPath.append_edges] using hs
      rcases hs' with hsA | hsB
      · exact Or.inl (eq_last_edge_of_mem_segment hA haA hsA hps)
      · exact Or.inr (eq_first_edge_of_mem_segment hB hbB hsB hps)
    have hinter : A.toSet ∩ B.toSet ⊆
        ({D.toDrawing.vertex (edgeSource e), p} : Set V) := by
      rcases show (A.append B).IsSimpleArcOrLoop from hAB ▸ D.cell_isSimpleArcOrLoop e with
        ⟨hS, _⟩ | ⟨heq', hL⟩
      · intro u hu
        exact Or.inr ((PolygonalPath.isSimple_append_iff.mp hS).2.2 hu)
      · let B' : PolygonalPath p (D.toDrawing.vertex (edgeSource e)) := B.cast rfl heq'
        have hBset : B'.toSet = B.toSet := PolygonalPath.toSet_cast B rfl heq'
        have hL' : (A.append B').IsSimpleLoop := by
          dsimp [B']
          rwa [← append_cast_right A B heq']
        intro u hu
        have : u ∈ A.toSet ∩ B'.toSet := ⟨hu.1, hBset ▸ hu.2⟩
        exact ((PolygonalPath.isSimpleLoop_append_iff hxp).mp hL').2.2 ▸ this
    have ha_not_other {f : E(G)} (hf : f ≠ e) : p ∉ (D.cell f).toSet := by
      intro hpf
      rw [← D.range_edgePath f] at hpf
      obtain ⟨t, rfl⟩ := hpf
      by_cases h0 : t = 0
      · exact hp_not_v (by rw [h0, Path.source]; exact ⟨_, rfl⟩)
      by_cases h1 : t = 1
      · exact hp_not_v (by rw [h1, Path.target]; exact ⟨_, rfl⟩)
      · exact (Drawing.pathInterior_edgePath_disjoint D.toDrawing hf.symm).notMem_of_mem_left hp
          ⟨t, ⟨lt_of_le_of_ne t.2.1 (Ne.symm h0), lt_of_le_of_ne t.2.2 h1⟩, rfl⟩
    have hcellCompact (f : E(G)) : IsCompact (D.cell f).toSet := by
      rw [PolygonalPath.toSet_eq_insert_biUnion]
      exact isCompact_singleton.union <|
        ((D.cell f).edges.finite_toSet).isCompact_biUnion fun _ _ ↦ isCompact_segment _ _
    let T : Set (V × V) := {s | s ∈ (D.cell e).edges ∧ p ∉ segment ℝ s.1 s.2}
    let Kcell : Set V := ⋃ s ∈ T, segment ℝ s.1 s.2
    let Kfor : Set V := range D.toDrawing.vertex ∪ ⋃ f ∈ {f : E(G) | f ≠ e}, (D.cell f).toSet
    let K : Set V := Kfor ∪ Kcell
    have hKclosed : IsClosed K := by
      refine IsClosed.union ?_ ?_
      · refine IsClosed.union ?_ ?_
        · have : Finite V(G) := inferInstance
          exact (Set.finite_range D.toDrawing.vertex).isCompact.isClosed
        · exact ((Set.toFinite _).isCompact_biUnion fun f _ ↦ hcellCompact f).isClosed
      · exact ((D.cell e).edges.finite_toSet.subset fun _ h ↦ h.1).isCompact_biUnion
          (fun _ _ ↦ isCompact_segment _ _) |>.isClosed
    have hpK : p ∉ K := by
      refine not_or.mpr ⟨?_, ?_⟩
      · refine not_or.mpr ⟨hp_not_v, ?_⟩
        intro hp'
        obtain ⟨f, hf, hpf⟩ := mem_iUnion₂.mp hp'
        exact ha_not_other hf hpf
      · intro hp'
        obtain ⟨s, hs, hseg⟩ := mem_iUnion₂.mp hp'
        exact hs.2 hseg
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
      constructor
      · intro ⟨hxball, hxsup⟩
        refine ⟨hxball, ?_⟩
        rw [Drawing.support_eq] at hxsup
        rcases hxsup with hxV | hxE
        · exact (hnotK hxball (Or.inl (Or.inl hxV))).elim
        · obtain ⟨f, hf⟩ := mem_iUnion.mp hxE
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
      · intro ⟨hxball, hxseg⟩
        refine ⟨hxball, ?_⟩
        have : x ∈ (D.cell e).toSet := by
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

private lemma coe_star_eq_sphere_inter_support {p : V} {ρ : ℝ} {Y : Finset V} {S : Set V}
    (hρ : 0 < ρ) (hYsph : ↑Y ⊆ sphere p ρ)
    (hstar : closedBall p ρ ∩ S = {p} ∪ ⋃ y ∈ Y, segment ℝ p y) :
    (Y : Set V) = sphere p ρ ∩ S := by
  ext y
  constructor
  · intro hy
    refine ⟨hYsph hy, ?_⟩
    have : y ∈ closedBall p ρ ∩ S := by
      rw [hstar]
      exact Or.inr (mem_iUnion₂.mpr ⟨y, hy, right_mem_segment _ _ _⟩)
    exact this.2
  · intro ⟨hysph, hysup⟩
    have hyball : y ∈ closedBall p ρ := sphere_subset_closedBall hysph
    have hy' : y ∈ ({p} : Set V) ∪ ⋃ y ∈ Y, segment ℝ p y := by
      rw [← hstar]; exact ⟨hyball, hysup⟩
    rcases hy' with hy' | hy'
    · have hyp : y = p := mem_singleton_iff.mp hy'
      have : dist p y = ρ := by
        simpa [PseudoMetricSpace.dist_comm] using mem_sphere.mp hysph
      rw [hyp, dist_self] at this
      exact (hρ.ne' this.symm).elim
    · obtain ⟨y', hy'Y, hyseg⟩ := mem_iUnion₂.mp hy'
      obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ := (segment_eq_image_lineMap (𝕜 := ℝ) p y').symm ▸ hyseg
      have hy'dist : dist p y' = ρ := by
        simpa [PseudoMetricSpace.dist_comm] using mem_sphere.mp (hYsph hy'Y)
      have htρ : t * dist p y' = dist p (AffineMap.lineMap p y' t) :=
        (PseudoMetricSpace.dist_comm (AffineMap.lineMap p y' t) p ▸
          dist_lineMap_left_of_nonneg p y' ht0).symm
      have : dist p (AffineMap.lineMap p y' t) = ρ := by
        simpa [PseudoMetricSpace.dist_comm] using mem_sphere.mp hysph
      have ht : t = 1 := by
        have hypos : 0 < dist p y' := by rw [hy'dist]; exact hρ
        have : t * dist p y' = (1 : ℝ) * dist p y' := by
          rw [htρ, this, hy'dist, one_mul]
        exact (mul_left_inj' hypos.ne').mp this
      simpa [ht] using hy'Y

private lemma pathInterior_edgePath_eq_toSet_sdiff (D : PLDrawing G V) (e : E(G)) :
    Drawing.pathInterior (D.toDrawing.edgePath e) =
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

omit [NormedAddCommGroup V] [NormedSpace ℝ V] in
private lemma cast_edges {x y x' y' : V} (P : PolygonalPath x y) (hx : x = x') (hy : y = y') :
    (P.cast hx hy).edges = P.edges := by
  subst hx; subst hy; rfl

private lemma IsSimpleLoop.hasNondegenerateEdges {x : V} {P : PolygonalPath x x}
    (h : P.IsSimpleLoop) : P.HasNondegenerateEdges := by
  cases P with
  | nil => exact (PolygonalPath.not_isSimpleLoop_nil h).elim
  | cons a b Q =>
    obtain ⟨hne, hQ, _⟩ := PolygonalPath.isSimpleLoop_cons_iff.mp h
    exact PolygonalPath.hasNondegenerateEdges_cons.mpr ⟨hne, hQ.hasNondegenerateEdges⟩

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
      rwa [cast_edges]
    exact (IsSimpleLoop.hasNondegenerateEdges hL' _ hb').symm

private lemma cell_in_ne_target (D : PLDrawing G V) (e : E(G)) {a : V}
    (ha : (a, D.toDrawing.vertex (edgeTarget e)) ∈ (D.cell e).edges) :
    a ≠ D.toDrawing.vertex (edgeTarget e) := by
  rcases D.cell_isSimpleArcOrLoop e with ⟨hS, _⟩ | ⟨heq, hL⟩
  · exact hS.hasNondegenerateEdges _ ha
  · have hL' : ((D.cell e).cast rfl heq).IsSimpleLoop := hL
    have ha0 : (a, D.toDrawing.vertex (edgeTarget e)) ∈ ((D.cell e).cast rfl heq).edges := by
      rwa [cast_edges]
    have heq_pair : (a, D.toDrawing.vertex (edgeTarget e)) =
        (a, D.toDrawing.vertex (edgeSource e)) := congrArg _ heq
    have ha' : (a, D.toDrawing.vertex (edgeSource e)) ∈ ((D.cell e).cast rfl heq).edges :=
      heq_pair ▸ ha0
    have hne : a ≠ D.toDrawing.vertex (edgeSource e) :=
      IsSimpleLoop.hasNondegenerateEdges hL' _ ha'
    have heq_ne : (a ≠ D.toDrawing.vertex (edgeSource e)) =
        (a ≠ D.toDrawing.vertex (edgeTarget e)) := by rw [heq]
    exact heq_ne ▸ hne

private lemma degree_eq_ncard_source_add_target [G.Finite] (v : V(G)) :
    G.degree v.1 =
      {e : E(G) | edgeSource e = v}.ncard + {e : E(G) | edgeTarget e = v}.ncard := by
  classical
  have : G.LocallyFinite := inferInstance
  let Outs : Set (E(G)) := {e | edgeSource e = v}
  let Ins : Set (E(G)) := {e | edgeTarget e = v}
  let L : Set (E(G)) := {e | edgeSource e = v ∧ edgeTarget e = v}
  let S : Set (E(G)) := {e | edgeSource e = v ∧ edgeTarget e ≠ v}
  let T : Set (E(G)) := {e | edgeTarget e = v ∧ edgeSource e ≠ v}
  have hOuts : Outs = L ∪ S := by
    ext e; constructor
    · intro he
      by_cases ht : edgeTarget e = v
      · exact Or.inl ⟨he, ht⟩
      · exact Or.inr ⟨he, ht⟩
    · exact fun h ↦ h.elim And.left And.left
  have hIns : Ins = L ∪ T := by
    ext e; constructor
    · intro he
      by_cases hs : edgeSource e = v
      · exact Or.inl ⟨hs, he⟩
      · exact Or.inr ⟨he, hs⟩
    · exact fun h ↦ h.elim And.right And.left
  have hLS : Disjoint L S :=
    disjoint_left.mpr fun _ hL hS ↦ hS.2 hL.2
  have hLT : Disjoint L T :=
    disjoint_left.mpr fun _ hL hT ↦ hT.2 hL.1
  have hST : Disjoint S T :=
    disjoint_left.mpr fun _ hS hT ↦ hT.2 hS.1
  have hL : {e | G.IsLoopAt e v.1} = Subtype.val '' L := by
    ext e; constructor
    · intro he
      refine ⟨⟨e, he.inc.edge_mem⟩, ?_, rfl⟩
      have hlink := isLink_edgeSource_edgeTarget ⟨e, he.inc.edge_mem⟩
      obtain ⟨h1, h2⟩ := he.eq_of_isLink hlink
      exact ⟨Subtype.ext h1.symm, Subtype.ext h2.symm⟩
    · rintro ⟨e', ⟨hs, ht⟩, rfl⟩
      have hlink := isLink_edgeSource_edgeTarget e'
      rw [hs, ht] at hlink
      exact isLink_self_iff.mp hlink
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

/- **Handoff to formalisation helper** (`exists_radius_vertex` degree conjunct).

The geometric star at a vertex image is already `exists_radius`. Relating `Y.card` to
`G.degree v` needs a bijection between sphere points and incidence ends at `v` (loop → two
outbound first/last cell segments; drawing injectivity ⇒ distinct ends give distinct directions).
The `Y` from `exists_radius` is opaque (radial points of *all* support segments through `p`).
Attempted rebuild from `E(G,v)` / `edgeSource`/`edgeTarget` stubs failed at matching opaque `Y` to
cell ends inside the star ball (unique-edge recovery, openSegment vertex exclusion). Provide either
(a) a lemma that at a vertex image the star segments are exactly the incident cell ends, plus
`radialPoint` injectivity, or (b) a constructive star rebuilt from incidences with shrunk `ρ`.
Scaffolding scale — not a tactic fill. Geometric equality without the degree conjunct is free from
`exists_radius`. -/
/-- At a vertex there is one radius per edge end: `degree` counts a loop twice, and a loop does
contribute two radii. -/
theorem exists_radius_vertex [G.Finite] (D : PLDrawing G V) (v : V(G)) :
    ∃ ρ > 0, ∃ Y : Finset V, ↑Y ⊆ sphere (D.toDrawing.vertex v) ρ ∧
      (Y.card : ℕ∞) = G.degree v.1 ∧
      closedBall (D.toDrawing.vertex v) ρ ∩ D.toDrawing.support =
        {D.toDrawing.vertex v} ∪ ⋃ y ∈ Y, segment ℝ (D.toDrawing.vertex v) y := by
  classical
  obtain ⟨ρ, hρ, Y, hYsph, hstar⟩ := D.exists_radius (Drawing.vertex_mem_support _ v)
  refine ⟨ρ, hρ, Y, hYsph, ?_, hstar⟩
  sorry

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
private lemma faceSet_disjoint_of_ne {X : Type*} [TopologicalSpace X] {G : Graph α β}
    (D : Drawing G X) {F G' : D.Face} (hne : F ≠ G') :
    Disjoint (D.faceSet F) (D.faceSet G') := by
  refine disjoint_left.mpr ?_
  rintro _ ⟨a, haF, rfl⟩ ⟨b, hbG, heq⟩
  have hab : a = b := Subtype.ext heq.symm
  subst hab
  have hF : F = ConnectedComponents.mk a := (mem_singleton_iff.mp haF).symm
  have hG : G' = ConnectedComponents.mk a := (mem_singleton_iff.mp hbG).symm
  exact hne (hF.trans hG.symm)

/-- **Sector extraction.** If the closed ball at `p` meets the drawing in a star, then any face
whose frontier reaches a point `q` of the open ball contains the image of a whole sector of the
punctured disk.

Stated for a general `q ∈ ball p ρ` rather than for `p` itself: two of the three call sites want
`q = p` and the third does not, and the argument never looks at which.  -/
private lemma exists_sector_subset_faceSet [G.Finite]
    (D : PLDrawing G (EuclideanSpace ℝ (Fin 2))) {p q : EuclideanSpace ℝ (Fin 2)}
    {ρ : ℝ} {Y : Finset (EuclideanSpace ℝ (Fin 2))} (hYne : Y.Nonempty)
    (hstar : closedBall p ρ ∩ D.toDrawing.support = {p} ∪ ⋃ y ∈ Y, segment ℝ p y)
    (hqball : q ∈ ball p ρ) {F : D.toDrawing.onePoint.Face} (hF : F ∈ D.facesAt q) :
    ∃ C ∈ sectors p ρ Y, (↑) '' C ⊆ D.toDrawing.onePoint.faceSet F := by
  have hnhds : (↑) '' (ball p ρ) ∈ 𝓝 (q : OnePoint (EuclideanSpace ℝ (Fin 2))) := by
    rw [OnePoint.nhds_coe_eq]
    exact Filter.image_mem_map (isOpen_ball.mem_nhds hqball)
  obtain ⟨z', ⟨hzU, hzF⟩⟩ :=
    mem_closure_iff_nhds.mp (frontier_subset_closure hF) ((↑) '' ball p ρ) hnhds
  obtain ⟨z, hzball, rfl⟩ := hzU
  have hzS : z ∉ D.toDrawing.support := by
    have : (z : OnePoint _) ∉ D.toDrawing.onePoint.support :=
      (D.toDrawing.onePoint.faceSet_disjoint_support F).notMem_of_mem_left hzF
    rw [Drawing.support_onePoint] at this
    exact fun hz ↦ this ⟨z, hz, rfl⟩
  have hzD : z ∈ diskMinusRadii p ρ Y := by
    refine ⟨hzball, fun hzrad ↦ hzS ?_⟩
    have hzsup : z ∈ closedBall p ρ ∩ D.toDrawing.support := by
      rw [hstar]
      exact Or.inr (by simpa [mem_iUnion] using hzrad)
    exact hzsup.2
  refine ⟨connectedComponentIn (diskMinusRadii p ρ Y) z, ⟨z, hzD, rfl⟩, ?_⟩
  have hCsub := connectedComponentIn_subset (diskMinusRadii p ρ Y) z
  have hconn : IsConnected
      ((↑) '' connectedComponentIn (diskMinusRadii p ρ Y) z :
        Set (OnePoint (EuclideanSpace ℝ (Fin 2)))) :=
    (isConnected_connectedComponentIn_iff.mpr hzD).image _ OnePoint.continuous_coe.continuousOn
  have himg : (↑) '' connectedComponentIn (diskMinusRadii p ρ Y) z ⊆
      D.toDrawing.onePoint.supportᶜ := by
    intro w hw
    obtain ⟨w0, hw0, rfl⟩ := hw
    have hw0D := hCsub hw0
    have hw0S : w0 ∉ D.toDrawing.support := by
      intro hwS
      have hw0mem : w0 ∈ closedBall p ρ ∩ D.toDrawing.support :=
        ⟨ball_subset_closedBall hw0D.1, hwS⟩
      rw [hstar] at hw0mem
      obtain rfl | hwY := hw0mem
      · exact hw0D.2 (by
          obtain ⟨y, hy⟩ := hYne
          exact mem_iUnion.mpr ⟨y, mem_iUnion.mpr ⟨hy, left_mem_segment _ _ _⟩⟩)
      exact hw0D.2 (by simpa [mem_iUnion] using hwY)
    rw [Drawing.support_onePoint]
    exact fun ⟨w1, hw1, heq⟩ ↦ hw0S (OnePoint.coe_injective heq ▸ hw1)
  have hz_mem : (z : OnePoint (EuclideanSpace ℝ (Fin 2))) ∈
      (↑) '' connectedComponentIn (diskMinusRadii p ρ Y) z :=
    ⟨z, mem_connectedComponentIn hzD, rfl⟩
  rw [D.toDrawing.onePoint.faceSet_eq_connectedComponentIn F hzF]
  exact hconn.isPreconnected.subset_connectedComponentIn hz_mem himg


/-- An open cell has at most two sides. -/
theorem ncard_facesAt_le_two [G.Finite] (D : PLDrawing G (EuclideanSpace ℝ (Fin 2))) {e : E(G)}
    {p : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ Drawing.pathInterior (D.toDrawing.edgePath e)) :
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
    (hp : p ∈ Drawing.pathInterior (D.toDrawing.edgePath e))
    (hq : q ∈ Drawing.pathInterior (D.toDrawing.edgePath e))
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
    {p q : EuclideanSpace ℝ (Fin 2)} (hp : p ∈ Drawing.pathInterior (D.toDrawing.edgePath e))
    (hq : q ∈ Drawing.pathInterior (D.toDrawing.edgePath e)) :
    D.facesAt p = D.facesAt q := by
  classical
  let PI := Drawing.pathInterior (D.toDrawing.edgePath e)
  have hPIc : IsConnected PI := by
    simpa only [PI, Drawing.pathInterior] using
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
