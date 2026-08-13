module

public import Matroid.ForMathlib.Geometry.PolygonalPath.Approximation
public import Matroid.ForMathlib.Analysis.Convex.RadialPoint

/-!
# Replacing a family of paths by disjoint polygonal arcs ending on given spheres

The analytic and geometric core of the PL reduction (Kuratowski `Status.md` §2.6, steps 3–6),
with no graph in it. `Matroid/Graph/Planarity/PLReduction.lean` supplies the graph bookkeeping —
which balls, which paths, which edges — and consumes these two statements.

## Main statements

* `exists_polygonalPath_family_of_disjoint` : finitely many pairwise disjoint compact paths, each
  avoiding a closed set of its own, can be replaced by polygonal paths with the same endpoints,
  still pairwise disjoint and still avoiding those closed sets.
* `exists_isSimple_radial` : a polygonal path running between two disjoint balls can be re-cut at
  its last exit and first entry and joined to the two centres by radii, giving an *embedded*
  polygonal arc meeting each ball in exactly one radius.

## Implementation notes

Both were `theorem`s inside `namespace Graph` in `PLReduction.lean`, where neither statement
mentioned a graph. Their proofs there carried local `mdist_comm` / `mdist_triangle` shims, because
`Graph.dist` shadows the metric `dist` inside that namespace; out here the shims are unnecessary
and are gone. See Kuratowski `Decisions.md` D14.

The ordering in `exists_isSimple_radial` is what Status.md §2.6 Step 5 insists on: the radii are
chosen using the *polyline's* last exit, not the original arc's. Two radii of one ball ending at
distinct sphere points meet only at the centre (`segment_radial_inter_eq_center`), which is what
makes the assembled arc embedded.
-/

@[expose] public section

universe u

open Function Set Topology Metric PolygonalPath
open scoped unitInterval

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]


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
  have : Fintype ι := Fintype.ofFinite _
  have hrange_nonempty (i : ι) : (range (Q i)).Nonempty := ⟨_, ⟨0, rfl⟩⟩
  have hrange_compact (i : ι) : IsCompact (range (Q i)) := isCompact_range (Q i).continuous
  have hrange_closed (i : ι) : IsClosed (range (Q i)) := (hrange_compact i).isClosed
  -- Status.md: empty minima default to `1`, encoded by adjoining `1` to the separation set.
  let pairSep (i j : ι) (hij : i ≠ j) : ℝ :=
    Classical.choose <|
      exists_pos_le_dist_of_disjoint (hrange_compact i) (hrange_closed j) (hQ hij)
  let kSep (i : ι) : ℝ :=
    Classical.choose <|
      exists_pos_le_dist_of_disjoint (hrange_compact i) (hK i) (hQK i)
  have hpairSep_spec (i j : ι) (hij : i ≠ j) :
      0 < pairSep i j hij ∧
        ∀ x ∈ range (Q i), ∀ y ∈ range (Q j), pairSep i j hij ≤ dist x y :=
    Classical.choose_spec <|
      exists_pos_le_dist_of_disjoint (hrange_compact i) (hrange_closed j) (hQ hij)
  have hkSep_spec (i : ι) :
      0 < kSep i ∧ ∀ x ∈ range (Q i), ∀ y ∈ K i, kSep i ≤ dist x y :=
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
    · grind
    · grind
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
  refine ⟨P, fun i j hij ↦ ?_, fun i ↦ ?_⟩
  · refine Disjoint.mono (hP i) (hP j) ?_
    refine disjoint_iff_inf_le.mpr fun z ⟨hzi, hzj⟩ ↦ ?_
    have hzi' := (Metric.mem_thickening_iff_infDist_lt (hrange_nonempty i)).mp hzi
    have hzj' := (Metric.mem_thickening_iff_infDist_lt (hrange_nonempty j)).mp hzj
    obtain ⟨x, hx, hxz⟩ := (infDist_lt_iff (hrange_nonempty i)).mp hzi'
    obtain ⟨y, hy, hyz⟩ := (infDist_lt_iff (hrange_nonempty j)).mp hzj'
    have hsep := (hpairSep_spec i j hij).2 x hx y hy
    have hlt : dist x y < pairSep i j hij := by
      have : dist x y < 2 * δ :=
        calc
          dist x y ≤ dist x z + dist z y := dist_triangle x z y
          _ = dist z x + dist z y := by rw [dist_comm x z]
          _ < δ + δ := add_lt_add hxz hyz
          _ = 2 * δ := by ring
      have h2 : 2 * δ ≤ (2 / 3) * pairSep i j hij := by
        have := hδ_le_pair i j hij
        nlinarith
      have h23 : (2 / 3 : ℝ) * pairSep i j hij < pairSep i j hij :=
        (mul_lt_iff_lt_one_left (hpairSep_spec i j hij).1).mpr (by norm_num)
      exact this.trans <| lt_of_le_of_lt h2 h23
    exact (hlt.not_ge hsep).elim
  refine Disjoint.mono_left (hP i) (disjoint_iff_inf_le.mpr fun z ⟨hzP, hzK⟩ ↦ ?_)
  have hz' := (Metric.mem_thickening_iff_infDist_lt (hrange_nonempty i)).mp hzP
  obtain ⟨x, hx, hxz⟩ := (infDist_lt_iff (hrange_nonempty i)).mp hz'
  have hsep := (hkSep_spec i).2 x hx z hzK
  have hlt : dist x z < kSep i := by
    have : dist x z < δ := by
      rwa [dist_comm]
    exact this.trans_le <|
      (hδ_le_k i).trans <|
        le_of_lt <| (mul_lt_iff_lt_one_left (hkSep_spec i).1).mpr (by norm_num : (1 / 3 : ℝ) < 1)
  exact (hlt.not_ge hsep).elim






theorem exists_isSimple_radial {cu cv : V} {ru rv : ℝ} (hru : 0 < ru) (hrv : 0 < rv)
    (hballs : Disjoint (closedBall cu ru) (closedBall cv rv)) {x y : V}
    (P : PolygonalPath x y) (hx : x ∈ closedBall cu ru) (hy : y ∈ closedBall cv rv) :
    ∃ (zu zv : V) (R : PolygonalPath cu cv), R.IsSimple ∧
      dist zu cu = ru ∧ dist zv cv = rv ∧
      R.toSet ∩ closedBall cu ru = segment ℝ cu zu ∧
      R.toSet ∩ closedBall cv rv = segment ℝ cv zv ∧
      R.toSet \ (ball cu ru ∪ ball cv rv) ⊆ P.toSet := by
  have hBu {z : V} (hz : dist z cu = ru) :
      segment ℝ cu z ⊆ closedBall cu ru :=
    (convex_closedBall cu ru).segment_subset (mem_closedBall_self hru.le)
      (mem_closedBall.mpr hz.le)
  have hBv {z : V} (hz : dist z cv = rv) :
      segment ℝ cv z ⊆ closedBall cv rv :=
    (convex_closedBall cv rv).segment_subset (mem_closedBall_self hrv.le)
      (mem_closedBall.mpr hz.le)
  obtain ⟨M, hM, hMP⟩ := P.exists_isSimple_toSet_subset
  have hMlen : 0 < M.length := M.length_pos_of_ne (fun h ↦ hballs.notMem_of_mem_left hx (h ▸ hy))
  have hinj : Injective M.toPath := (injective_toPath_iff M).mpr ⟨hM, hMlen⟩
  obtain ⟨τ, τv, hτlt, hzu_dist, hzv_dist, hmid_u, hmid_v⟩ :=
    M.toPath.exists_lastExit_firstEntry hballs hx hy
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
    have hQsub : Q.toSet ⊆ range M.toPath :=
      (hQ_subset_B.trans hB_subset_M).trans (M.toSet_eq_range_toPath ▸ Subset.rfl)
    have hQ : M.toPath '' Icc τ τv ⊆ Q.toSet :=
      Path.image_Icc_subset_of_isConnected hinj Q.isConnected_toSet hQsub
        (by simp [zu]) (by simp [zv])
    refine subset_antisymm ?_ hQ
    intro w hwQ
    obtain ⟨t, rfl⟩ : w ∈ range M.toPath := hQsub hwQ
    have ht_ge : τ ≤ t := by
      have : M.toPath t ∈ B.toSet := hQ_subset_B hwQ
      rw [hB_eq] at this
      obtain ⟨tM, htM, htMeq⟩ := this
      exact (hinj htMeq) ▸ htM.1
    refine ⟨t, ⟨ht_ge, ?_⟩, rfl⟩
    by_contra ht
    have ht' : τv < t := lt_of_not_ge ht
    have h2sub : (B.breakAt hzv_toSet).2.toSet ⊆ range M.toPath :=
      (((breakAt_toSet_union (P := B) (ha := hzv_toSet)).symm ▸ subset_union_right).trans
        hB_subset_M).trans (M.toSet_eq_range_toPath ▸ Subset.rfl)
    have htail : M.toPath '' Icc τv (1 : I) ⊆ (B.breakAt hzv_toSet).2.toSet :=
      Path.image_Icc_subset_of_isConnected hinj (B.breakAt hzv_toSet).2.isConnected_toSet h2sub
        (by simp [zv]) (by simp [Path.target])
    have hinter : M.toPath t ∈ Q.toSet ∩ (B.breakAt hzv_toSet).2.toSet :=
      ⟨hwQ, htail ⟨t, ⟨ht'.le, le_top⟩, rfl⟩⟩
    rw [hQB, mem_singleton_iff] at hinter
    exact ht'.ne (hinj (by simpa [zv] using hinter)).symm
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
    obtain hwu | hwQ := hw'.1
    · exact (hballs.notMem_of_mem_left (hBu hzu_dist hwu) hwBv).elim
    exact hQ_v ⟨hwQ, hwBv⟩
  refine ⟨zu, zv, R, hRsimple, hzu_dist, hzv_dist, ?_, ?_, fun w hw ↦ ?_⟩
  · refine subset_antisymm ?_ ?_
    · intro w hw
      have hwR : w ∈ segment ℝ cu zu ∪ Q.toSet ∪ segment ℝ zv cv := hR_toSet ▸ hw.1
      obtain hwuQ | hwv := hwR
      · obtain hwu | hwQ := hwuQ
        · exact hwu
        · exact (mem_singleton_iff.mp (hQ_u ⟨hwQ, hw.2⟩)) ▸ right_mem_segment ℝ cu zu
      · exact (hballs.notMem_of_mem_left hw.2
          (hBv hzv_dist (segment_symm (𝕜 := ℝ) zv cv ▸ hwv))).elim
    · grind
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
  obtain hwuQ | hwv : w ∈ segment ℝ cu zu ∪ Q.toSet ∪ segment ℝ zv cv := hR_toSet ▸ hw.1
  · obtain hwu | hwQ := hwuQ
    · have : w = zu := by
        have : w ∈ segment ℝ cu zu \ ball cu ru := ⟨hwu, (fun h ↦ hw.2 (Or.inl h))⟩
        rwa [segment_diff_ball_eq_singleton hru hzu_dist, mem_singleton_iff] at this
      exact hMP (this ▸ hzu_toSet)
    · exact hMP (hB_subset_M (hQ_subset_B hwQ))
  have : w = zv := by
    have heq : segment ℝ zv cv \ ball cv rv = {zv} := by
      rw [segment_symm]
      exact segment_diff_ball_eq_singleton hrv (dist_comm zv cv ▸ hzv_dist)
    have : w ∈ segment ℝ zv cv \ ball cv rv := ⟨hwv, (fun h ↦ hw.2 (Or.inr h))⟩
    rwa [heq, mem_singleton_iff] at this
  exact hMP (hB_subset_M (this ▸ hzv_toSet))



end
