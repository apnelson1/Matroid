module

public import Matroid.MiniTauCeti.JCT.Geometry.PolygonalPath.Approximation
public import Matroid.MiniTauCeti.JCT.Geometry.PolygonalPath.SegmentFigure
public import Mathlib.Algebra.Order.Field.Pi
public import Mathlib.Order.Filter.Bases.Finite

/-!
# Polygonal replacement of finite families of primitive links

The geometric construction uses sets and preserves primitive links, including loops. Each
replacement stays in its own prescribed open neighborhood and has the same endpoint incidences.
Paths are chosen only inside proofs, for cutting and polygonal approximation.
-/

@[expose] public section

open Function Set Topology Metric PolygonalPath
open scoped unitInterval

section

variable {V : Type*} [SeminormedAddCommGroup V] [NormedSpace ℝ V]

/-- Replace the two ends of `γ` by radii to `cu` and `cv`, keeping the subpath from its
last visit to the first closed ball to its first subsequent visit to the second. -/
noncomputable def Path.radialSet {x y : V} (γ : Path x y) (cu cv : V) (ru rv : ℝ) : Set V :=
  let t := γ.lastVisit (closedBall cu ru)
  let s := γ.firstVisitAfter (closedBall cv rv) t
  segment ℝ cu (γ t) ∪ range (γ.subpath t s) ∪ segment ℝ (γ s) cv

lemma Path.isSegmentFigure_radialSet {x y : V} (γ : Path x y) (cu cv : V) (ru rv : ℝ)
    (hpoly : IsSegmentFigure (range (γ.subpath (γ.lastVisit (closedBall cu ru))
      (γ.firstVisitAfter (closedBall cv rv) (γ.lastVisit (closedBall cu ru)))))) :
    IsSegmentFigure (γ.radialSet cu cv ru rv) :=
  ((isSegmentFigure_segment _ _).union hpoly).union (isSegmentFigure_segment _ _)

end

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

private lemma radialSet_geometry {cu cv : V} {ru rv : ℝ}
    (hballs : Disjoint (closedBall cu ru) (closedBall cv rv)) {x y : V} (γ : Path x y)
    (hx : x ∈ closedBall cu ru) (hy : y ∈ closedBall cv rv) :
    let t := γ.lastVisit (closedBall cu ru)
    let s := γ.firstVisitAfter (closedBall cv rv) t
    dist (γ t) cu = ru ∧ dist (γ s) cv = rv ∧
      γ.radialSet cu cv ru rv ∩ closedBall cu ru = segment ℝ cu (γ t) ∧
      γ.radialSet cu cv ru rv ∩ closedBall cv rv = segment ℝ cv (γ s) := by
  let t := γ.lastVisit (closedBall cu ru)
  let s := γ.firstVisitAfter (closedBall cv rv) t
  obtain ⟨hts, ht, hs, hleft, hright⟩ := γ.lastVisit_firstVisitAfter_spec
    (isClosed_closedBall.preimage γ.continuous)
    (isClosed_Ici.inter (isClosed_closedBall.preimage γ.continuous)) (hballs.preimage γ) hx hy
  have hdistu : dist (γ t) cu = ru := frontier_closedBall_subset_sphere ht
  have hdistv : dist (γ s) cv = rv := frontier_closedBall_subset_sphere hs
  have hQu : range (γ.subpath t s) ∩ closedBall cu ru = {γ t} := by
    rw [γ.range_subpath_of_le _ _ hts.le, ← image_inter_preimage, hleft, image_singleton]
  have hQv : range (γ.subpath t s) ∩ closedBall cv rv = {γ s} := by
    rw [γ.range_subpath_of_le _ _ hts.le, ← image_inter_preimage, hright, image_singleton]
  have hBu : segment ℝ cu (γ t) ⊆ closedBall cu ru := by
    simpa only [dist_comm cu (γ t), hdistu] using segment_subset_closedBall_left cu (γ t)
  have hBv : segment ℝ (γ s) cv ⊆ closedBall cv rv := by
    simpa only [hdistv] using segment_subset_closedBall_right (γ s) cv
  refine ⟨hdistu, hdistv, ?_, ?_⟩
  · change (segment ℝ cu (γ t) ∪ range (γ.subpath t s) ∪ segment ℝ (γ s) cv) ∩
      closedBall cu ru = segment ℝ cu (γ t)
    rw [union_inter_distrib_right, union_inter_distrib_right, inter_eq_left.mpr hBu,
      hQu, (hballs.symm.mono_left hBv).inter_eq, union_empty]
    exact union_eq_left.mpr (singleton_subset_iff.mpr (right_mem_segment ..))
  change (segment ℝ cu (γ t) ∪ range (γ.subpath t s) ∪ segment ℝ (γ s) cv) ∩
    closedBall cv rv = segment ℝ cv (γ s)
  rw [union_inter_distrib_right, union_inter_distrib_right, inter_eq_left.mpr hBv,
    hQv, (hballs.mono_left hBu).inter_eq, empty_union]
  rw [segment_symm (𝕜 := ℝ) (γ s) cv]
  exact union_eq_right.mpr (singleton_subset_iff.mpr (right_mem_segment ..))

lemma Path.radialSet_inter_closedBall_left {cu cv : V} {ru rv : ℝ}
    (hballs : Disjoint (closedBall cu ru) (closedBall cv rv)) {x y : V} (γ : Path x y)
    (hx : x ∈ closedBall cu ru) (hy : y ∈ closedBall cv rv) :
    γ.radialSet cu cv ru rv ∩ closedBall cu ru =
      segment ℝ cu (γ (γ.lastVisit (closedBall cu ru))) :=
  (radialSet_geometry hballs γ hx hy).2.2.1

lemma Path.radialSet_inter_closedBall_right {cu cv : V} {ru rv : ℝ}
    (hballs : Disjoint (closedBall cu ru) (closedBall cv rv)) {x y : V} (γ : Path x y)
    (hx : x ∈ closedBall cu ru) (hy : y ∈ closedBall cv rv) :
    γ.radialSet cu cv ru rv ∩ closedBall cv rv =
      segment ℝ cv (γ (γ.firstVisitAfter (closedBall cv rv) (γ.lastVisit (closedBall cu ru)))) :=
  (radialSet_geometry hballs γ hx hy).2.2.2

lemma Path.radialSet_diff_ball_eq_middle_diff {cu cv : V} {ru rv : ℝ} {x y : V} (γ : Path x y)
    (hu : dist (γ (γ.lastVisit (closedBall cu ru))) cu = ru)
    (hv : dist (γ (γ.firstVisitAfter (closedBall cv rv)
      (γ.lastVisit (closedBall cu ru)))) cv = rv) :
    γ.radialSet cu cv ru rv \ (ball cu ru ∪ ball cv rv) =
      range (γ.subpath (γ.lastVisit (closedBall cu ru))
        (γ.firstVisitAfter (closedBall cv rv) (γ.lastVisit (closedBall cu ru)))) \
          (ball cu ru ∪ ball cv rv) := by
  let t := γ.lastVisit (closedBall cu ru)
  let s := γ.firstVisitAfter (closedBall cv rv) t
  have hQu : segment ℝ cu (γ t) \ ball cu ru = {γ t} := segment_diff_ball_eq_singleton hu
  have hQv : segment ℝ (γ s) cv \ ball cv rv = {γ s} := by
    rw [segment_symm]
    exact segment_diff_ball_eq_singleton hv
  apply subset_antisymm
  · rintro w ⟨(hw | hw) | hw, hout⟩
    · have heq : w = γ t := hQu.subset ⟨hw, fun h ↦ hout (Or.inl h)⟩
      exact ⟨heq ▸ (γ.subpath t s).source_mem_range, hout⟩
    · exact ⟨hw, hout⟩
    have heq : w = γ s := hQv.subset ⟨hw, fun h ↦ hout (Or.inr h)⟩
    exact ⟨heq ▸ (γ.subpath t s).target_mem_range, hout⟩
  rintro w ⟨hw, hout⟩
  exact ⟨Or.inl (Or.inr hw), hout⟩

lemma Path.radialSet_diff_ball_eq_middle {cu cv : V} {ru rv : ℝ}
    (hballs : Disjoint (closedBall cu ru) (closedBall cv rv)) {x y : V} (γ : Path x y)
    (hx : x ∈ closedBall cu ru) (hy : y ∈ closedBall cv rv) :
    γ.radialSet cu cv ru rv \ (ball cu ru ∪ ball cv rv) =
      range (γ.subpath (γ.lastVisit (closedBall cu ru))
        (γ.firstVisitAfter (closedBall cv rv) (γ.lastVisit (closedBall cu ru)))) := by
  let t := γ.lastVisit (closedBall cu ru)
  let s := γ.firstVisitAfter (closedBall cv rv) t
  obtain ⟨hts, ht, hs, hleft, hright⟩ := γ.lastVisit_firstVisitAfter_spec
    (isClosed_closedBall.preimage γ.continuous)
    (isClosed_Ici.inter (isClosed_closedBall.preimage γ.continuous)) (hballs.preimage γ) hx hy
  have hu : dist (γ t) cu = ru := frontier_closedBall_subset_sphere ht
  have hv : dist (γ s) cv = rv := frontier_closedBall_subset_sphere hs
  have hQu : range (γ.subpath t s) ∩ closedBall cu ru = {γ t} := by
    rw [γ.range_subpath_of_le _ _ hts.le, ← image_inter_preimage, hleft, image_singleton]
  have hQv : range (γ.subpath t s) ∩ closedBall cv rv = {γ s} := by
    rw [γ.range_subpath_of_le _ _ hts.le, ← image_inter_preimage, hright, image_singleton]
  rw [γ.radialSet_diff_ball_eq_middle_diff hu hv]
  apply sdiff_eq_left.mpr
  apply disjoint_left.mpr
  rintro z hz (hzu | hzv)
  · have heq : z = γ t := hQu.subset ⟨hz, ball_subset_closedBall hzu⟩
    exact (mem_ball.mp hzu).ne (by simpa only [heq] using hu)
  have heq : z = γ s := hQv.subset ⟨hz, ball_subset_closedBall hzv⟩
  exact (mem_ball.mp hzv).ne (by simpa only [heq] using hv)

lemma Path.isPrimitiveLink_radialSet {cu cv : V} {ru rv : ℝ}
    (hballs : Disjoint (closedBall cu ru) (closedBall cv rv)) {x y : V}
    (γ : Path x y)
    (hmid : IsPrimitiveLink
      (range (γ.subpath (γ.lastVisit (closedBall cu ru))
        (γ.firstVisitAfter (closedBall cv rv) (γ.lastVisit (closedBall cu ru)))))
      (γ (γ.lastVisit (closedBall cu ru)))
      (γ (γ.firstVisitAfter (closedBall cv rv) (γ.lastVisit (closedBall cu ru)))))
    (hx : x ∈ closedBall cu ru) (hy : y ∈ closedBall cv rv) :
    IsPrimitiveLink (γ.radialSet cu cv ru rv) cu cv := by
  let τ := γ.lastVisit (closedBall cu ru)
  let τv := γ.firstVisitAfter (closedBall cv rv) τ
  obtain ⟨hτlt, hzu, hzv, hmid_u, hmid_v⟩ := γ.lastVisit_firstVisitAfter_spec
    (isClosed_closedBall.preimage γ.continuous)
    (isClosed_Ici.inter (isClosed_closedBall.preimage γ.continuous))
    (hballs.preimage γ) hx hy
  have hzu_dist : dist (γ τ) cu = ru := frontier_closedBall_subset_sphere hzu
  have hzv_dist : dist (γ τv) cv = rv := frontier_closedBall_subset_sphere hzv
  have hru : 0 ≤ ru := hzu_dist ▸ dist_nonneg
  have hmid_u : (γ '' Icc τ τv) ∩ closedBall cu ru = {γ τ} := by
    rw [← image_inter_preimage, hmid_u, image_singleton]
  have hmid_v : (γ '' Icc τ τv) ∩ closedBall cv rv = {γ τv} := by
    rw [← image_inter_preimage, hmid_v, image_singleton]
  set zu := γ τ
  set zv := γ τv
  let Q := range (γ.subpath τ τv)
  have hQlink : IsPrimitiveLink Q zu zv := hmid
  have hQsub : Q ⊆ γ '' Icc τ τv := (γ.range_subpath_of_le _ _ hτlt.le).le
  have hQ_u : Q ∩ closedBall cu ru ⊆ {zu} := by
    rw [← hmid_u]
    exact inter_subset_inter_left _ hQsub
  have hQ_v : Q ∩ closedBall cv rv ⊆ {zv} := by
    rw [← hmid_v]
    exact inter_subset_inter_left _ hQsub
  have hBu : segment ℝ cu zu ⊆ closedBall cu ru := by
    simpa only [dist_comm cu zu, hzu_dist] using segment_subset_closedBall_left cu zu
  have hBv : segment ℝ zv cv ⊆ closedBall cv rv := by
    simpa only [hzv_dist] using segment_subset_closedBall_right zv cv
  have hzz : zu ≠ zv := fun h ↦ hballs.notMem_of_mem_left
    (mem_closedBall.mpr hzu_dist.le) (h ▸ mem_closedBall.mpr hzv_dist.le)
  have hjoin : IsPrimitiveLink (segment ℝ cu zu ∪ Q) cu zv := by
    by_cases heq : cu = zu
    · have hset : segment ℝ cu zu ∪ Q = Q := by
        rw [heq, segment_same]
        exact union_eq_right.mpr (singleton_subset_iff.mpr hQlink.left_mem)
      rw [hset, heq]
      exact hQlink
    exact (isPrimitiveLink_segment heq).union hQlink heq hzz
      fun w hw ↦ hQ_u ⟨hw.2, hBu hw.1⟩
  change IsPrimitiveLink (segment ℝ cu zu ∪ Q ∪ segment ℝ zv cv) cu cv
  by_cases heq : zv = cv
  · have hset : segment ℝ cu zu ∪ Q ∪ segment ℝ zv cv = segment ℝ cu zu ∪ Q := by
      rw [← heq, segment_same]
      exact union_eq_left.mpr (singleton_subset_iff.mpr hjoin.right_mem)
    rw [hset, ← heq]
    exact hjoin
  apply hjoin.union (isPrimitiveLink_segment heq) (fun h ↦ hballs.notMem_of_mem_left
    (mem_closedBall_self hru) (h ▸ mem_closedBall.mpr hzv_dist.le)) heq
  rintro w ⟨hw | hw, hv⟩
  · exact ((hballs.mono hBu hBv).notMem_of_mem_left hw hv).elim
  exact hQ_v ⟨hw, hBv hv⟩

lemma Path.isSegmentFigure_radialSet_of_range {x y : V} (γ : Path x y)
    (cu cv : V) (ru rv : ℝ) (hpoly : IsSegmentFigure (range γ)) :
    IsSegmentFigure (γ.radialSet cu cv ru rv) := by
  apply γ.isSegmentFigure_radialSet
  apply hpoly.of_isClosed_isPreconnected (by rw [γ.range_subpath]; exact image_subset_range ..)
    (isCompact_range (γ.subpath _ _).continuous).isClosed
    (γ.subpath _ _).range_isPathConnected.isConnected.isPreconnected

lemma Path.IsPrimitive.isPrimitiveLink_radialSet {cu cv : V} {ru rv : ℝ}
    (hballs : Disjoint (closedBall cu ru) (closedBall cv rv)) {x y : V}
    {γ : Path x y} (hγ : γ.IsPrimitive)
    (hx : x ∈ closedBall cu ru) (hy : y ∈ closedBall cv rv) :
    IsPrimitiveLink (γ.radialSet cu cv ru rv) cu cv := by
  apply γ.isPrimitiveLink_radialSet hballs _ hx hy
  have hts := (γ.lastVisit_firstVisitAfter_spec
    (isClosed_closedBall.preimage γ.continuous)
    (isClosed_Ici.inter (isClosed_closedBall.preimage γ.continuous))
    (hballs.preimage γ) hx hy).1
  exact (hγ.subpath hts.ne).isPrimitiveLink

lemma Path.radialSet_diff_ball_subset_range {cu cv : V} {ru rv : ℝ}
    {x y : V} (γ : Path x y)
    (hu : dist (γ (γ.lastVisit (closedBall cu ru))) cu = ru)
    (hv : dist (γ (γ.firstVisitAfter (closedBall cv rv)
      (γ.lastVisit (closedBall cu ru)))) cv = rv) :
    γ.radialSet cu cv ru rv \ (ball cu ru ∪ ball cv rv) ⊆ range γ := by
  rw [γ.radialSet_diff_ball_eq_middle_diff hu hv]
  apply sdiff_subset.trans
  rw [γ.range_subpath]
  exact image_subset_range ..

/-- A polygonal primitive link between disjoint closed balls admits a radial replacement.
For a specified parametrization, the actual replacement is `Path.radialSet`. -/
theorem IsPrimitiveLink.exists_radial {cu cv : V} {ru rv : ℝ}
    (hballs : Disjoint (closedBall cu ru) (closedBall cv rv)) {x y : V}
    {L : Set V} (hL : IsPrimitiveLink L x y) (hpoly : IsSegmentFigure L)
    (hx : x ∈ closedBall cu ru) (hy : y ∈ closedBall cv rv) :
    ∃ (zu zv : V) (S : Set V), IsPrimitiveLink S cu cv ∧ IsSegmentFigure S ∧
      dist zu cu = ru ∧ dist zv cv = rv ∧
      S ∩ closedBall cu ru = segment ℝ cu zu ∧
      S ∩ closedBall cv rv = segment ℝ cv zv ∧
      S \ (ball cu ru ∪ ball cv rv) ⊆ L ∧ zu ∈ L ∧ zv ∈ L := by
  obtain ⟨γ, hγ, rfl⟩ := hL
  obtain ⟨hu, hv, hleft, hright⟩ := radialSet_geometry hballs γ hx hy
  exact ⟨_, _, γ.radialSet cu cv ru rv, hγ.isPrimitiveLink_radialSet hballs hx hy,
    γ.isSegmentFigure_radialSet_of_range cu cv ru rv hpoly, hu, hv, hleft, hright,
    γ.radialSet_diff_ball_subset_range hu hv, mem_range_self _, mem_range_self _⟩

private theorem exists_polygonal_arc_family
    {ι : Type*} [Finite ι] {Z : Set V} [Finite Z] {a b : ι → Z}
    (F : ∀ i, Path (a i).1 (b i).1)
    (hFV : ∀ i, range (F i) ∩ Z ⊆ {(a i).1, (b i).1})
    (hFF : Pairwise fun i j ↦ range (F i) ∩ range (F j) ⊆ Z)
    (hne : ∀ i, a i ≠ b i) (U : ι → Set V) (hU : ∀ i, IsOpen (U i))
    (hFU : ∀ i, range (F i) ⊆ U i) :
    ∃ C : ι → Set V, (∀ i, IsPrimitiveLink (C i) (a i).1 (b i).1) ∧
      (∀ i, IsSegmentFigure (C i)) ∧
      (∀ i, C i ∩ Z = {(a i).1, (b i).1}) ∧
      (Pairwise fun i j ↦ C i ∩ C j ⊆ Z) ∧ ∀ i, C i ⊆ U i := by
  classical
  choose δ hδ hδU using fun i ↦
    (isCompact_range (F i).continuous).exists_thickening_subset_open (hU i) (hFU i)
  obtain ⟨ε, hε, hεδ⟩ := Pi.exists_forall_pos_add_lt hδ
  simp only [zero_add] at hεδ
  obtain ⟨r, hpos, hsmall, hdisj, hav⟩ := exists_disjoint_closedBall_avoiding
    (fun i ↦ range (F i)) (fun i ↦ (isCompact_range (F i).continuous).isClosed)
    (fun _ : Z ↦ ε) (fun _ ↦ hε)
  have havoid (i) (x : Z) (hxa : x ≠ a i) (hxb : x ≠ b i) :
      Disjoint (range (F i)) (closedBall x.1 (r x)) := by
    apply hav i x
    intro hx
    obtain ha | hb := hFV i ⟨hx, x.2⟩
    · exact hxa (Subtype.ext ha)
    · exact hxb (Subtype.ext hb)
  let t i := (F i).lastVisit (closedBall (a i).1 (r (a i)))
  let s i := (F i).firstVisitAfter (closedBall (b i).1 (r (b i))) (t i)
  have hcut i := (F i).lastVisit_firstVisitAfter_spec
    (isClosed_closedBall.preimage (F i).continuous)
    (isClosed_Ici.inter (isClosed_closedBall.preimage (F i).continuous))
    ((hdisj (hne i)).preimage (F i))
    (mem_closedBall_self (hpos _).le) (mem_closedBall_self (hpos _).le)
  have hts i : t i < s i := (hcut i).1
  have hdistu i : dist (F i (t i)) (a i).1 = r (a i) :=
    frontier_closedBall_subset_sphere (hcut i).2.1
  have hdistv i : dist (F i (s i)) (b i).1 = r (b i) :=
    frontier_closedBall_subset_sphere (hcut i).2.2.1
  have hinteru i : (F i '' Icc (t i) (s i)) ∩ closedBall (a i).1 (r (a i)) = {F i (t i)} := by
    rw [← image_inter_preimage, (hcut i).2.2.2.1, image_singleton]
  have hinterv i : (F i '' Icc (t i) (s i)) ∩ closedBall (b i).1 (r (b i)) = {F i (s i)} := by
    rw [← image_inter_preimage, (hcut i).2.2.2.2, image_singleton]
  let Q := fun i ↦ (F i).subpath (t i) (s i)
  have hQr (i) : range (Q i) = F i '' Icc (t i) (s i) :=
    Path.range_subpath_of_le _ _ _ (hts i).le
  have hQsub (i) : range (Q i) ⊆ range (F i) := hQr i ▸ image_subset_range ..
  have center_notMem {S : Set V} {c z : V} {ρ : ℝ} (hρ : 0 < ρ)
      (hz : dist z c = ρ) (hS : S ∩ closedBall c ρ = {z}) : c ∉ S := by
    intro hc
    have heq : c = z := hS.subset ⟨hc, mem_closedBall_self hρ.le⟩
    exact hρ.ne' (by simpa [← heq] using hz.symm)
  have hQZ (i) : Disjoint (range (Q i)) Z := by
    refine disjoint_left.mpr fun w hw hwZ ↦ ?_
    obtain rfl | rfl := hFV i ⟨hQsub i hw, hwZ⟩
    · exact center_notMem (hpos _) (hdistu i) (hinteru i) (hQr i ▸ hw)
    · exact center_notMem (hpos _) (hdistv i) (hinterv i) (hQr i ▸ hw)
  let u i := F i (t i)
  let v i := F i (s i)
  have hQavoid (i) (x : Z) (hxa : x ≠ a i) (hxb : x ≠ b i) :=
    (havoid i x hxa hxb).mono_left (hQsub i)
  have hQdisj : Pairwise fun i j ↦ Disjoint (range (Q i)) (range (Q j)) :=
    fun i j hij ↦ disjoint_left.mpr fun w hwi hwj ↦
      (hQZ i).notMem_of_mem_left hwi (hFF hij ⟨hQsub i hwi, hQsub j hwj⟩)
  let K (i : ι) : Set V :=
    (⋃ x ∈ {x : Z | x ≠ a i ∧ x ≠ b i}, closedBall x.1 (r x)) ∪
      (thickening ε (range (F i)))ᶜ
  have hKclosed (i) : IsClosed (K i) :=
    ((toFinite _).isClosed_biUnion fun _ _ ↦ isClosed_closedBall).union
      isOpen_thickening.isClosed_compl
  have hQK (i) : Disjoint (range (Q i)) (K i) := by
    refine disjoint_left.mpr fun w hwQ hwK ↦ ?_
    obtain hwball | hwfar := hwK
    · obtain ⟨x, hx, hwB⟩ := mem_iUnion₂.mp hwball
      exact (hQavoid i x hx.1 hx.2).notMem_of_mem_left hwQ hwB
    · exact hwfar (self_subset_thickening hε _ (hQsub i hwQ))
  have hd : Pairwise fun i j ↦ Disjoint (𝓝ˢ (range (Q i))) (𝓝ˢ (range (Q j))) :=
    fun i j hij ↦ disjoint_nhdsSet_nhdsSet (isCompact_range (Q i).continuous).isClosed
      (isCompact_range (Q j).continuous).isClosed (hQdisj hij)
  obtain ⟨O, hO, hdisjO⟩ := hd.exists_mem_filter_basis_of_disjoint fun i ↦ hasBasis_nhdsSet _
  have hjoined (i) : JoinedIn (O i ∩ (K i)ᶜ) (u i) (v i) :=
    ⟨Q i, fun t ↦ ⟨(hO i).2 (mem_range_self t),
      (hQK i).subset_compl_right (mem_range_self t)⟩⟩
  choose P hPsimple hPO using fun i ↦
    (hjoined i).exists_isSimple_polygonalPath_of_open
      ((hO i).1.inter (hKclosed i).isOpen_compl)
  have hPdisj : Pairwise fun i j ↦ Disjoint (P i).toSet (P j).toSet :=
    fun i j hij ↦ (hdisjO hij).mono ((hPO i).trans inter_subset_left)
      ((hPO j).trans inter_subset_left)
  have hPK (i) : Disjoint (P i).toSet (K i) :=
    disjoint_left.mpr fun w hw ↦ (hPO i hw).2
  have hPnear (i) : (P i).toSet ⊆ thickening ε (range (F i)) := by
    intro w hw
    by_contra hfar
    exact (hPK i).notMem_of_mem_left hw (Or.inr hfar)
  have huv (i) : u i ≠ v i := by
    intro h
    exact (hdisj (hne i)).notMem_of_mem_left (mem_closedBall.mpr (hdistu i).le)
      (show u i ∈ closedBall (b i).1 (r (b i)) from
        h ▸ (show v i ∈ closedBall (b i).1 (r (b i)) from mem_closedBall.mpr (hdistv i).le))
  let τ i := (P i).toPath.lastVisit (closedBall (a i).1 (r (a i)))
  let τv i := (P i).toPath.firstVisitAfter (closedBall (b i).1 (r (b i))) (τ i)
  let za i := (P i).toPath (τ i)
  let zb i := (P i).toPath (τv i)
  let C i := (P i).toPath.radialSet (a i).1 (b i).1 (r (a i)) (r (b i))
  have hgeometry i := radialSet_geometry (hdisj (hne i)) (P i).toPath
    (mem_closedBall.mpr (hdistu i).le) (mem_closedBall.mpr (hdistv i).le)
  have hs i : IsPrimitiveLink (C i) (a i).1 (b i).1 :=
    ((hPsimple i).isPrimitive ((P i).length_pos_of_ne (huv i))).isPrimitiveLink_radialSet
      (hdisj (hne i))
      (mem_closedBall.mpr (hdistu i).le) (mem_closedBall.mpr (hdistv i).le)
  have hpoly i : IsSegmentFigure (C i) :=
    (P i).toPath.isSegmentFigure_radialSet_of_range _ _ _ _
      (by rw [← toSet_eq_range_toPath]; exact (P i).isSegmentFigure_toSet)
  have hza i : dist (za i) (a i).1 = r (a i) := (hgeometry i).1
  have hzb i : dist (zb i) (b i).1 = r (b i) := (hgeometry i).2.1
  have hCa i : C i ∩ closedBall (a i).1 (r (a i)) = segment ℝ (a i).1 (za i) :=
    (hgeometry i).2.2.1
  have hCb i : C i ∩ closedBall (b i).1 (r (b i)) = segment ℝ (b i).1 (zb i) :=
    (hgeometry i).2.2.2
  have hCmid i : C i \ (ball (a i).1 (r (a i)) ∪ ball (b i).1 (r (b i))) ⊆ (P i).toSet := by
    rw [toSet_eq_range_toPath]
    exact (P i).toPath.radialSet_diff_ball_subset_range (hza i) (hzb i)
  have hzaP i : za i ∈ (P i).toSet := by rw [toSet_eq_range_toPath]; exact mem_range_self _
  have hzbP i : zb i ∈ (P i).toSet := by rw [toSet_eq_range_toPath]; exact mem_range_self _
  have hCcover (i) : C i ⊆
      (ball (a i).1 (r (a i)) ∪ ball (b i).1 (r (b i))) ∪ (P i).toSet :=
    sdiff_subset_iff.mp (hCmid i)
  have hCavoid (i) (x : Z) (hxa : x ≠ a i) (hxb : x ≠ b i) :
      Disjoint (C i) (closedBall x.1 (r x)) := by
    apply Disjoint.mono_left (hCcover i)
    refine disjoint_union_left.mpr ⟨disjoint_union_left.mpr
      ⟨(hdisj hxa.symm).mono_left ball_subset_closedBall,
        (hdisj hxb.symm).mono_left ball_subset_closedBall⟩, (hPK i).mono_right ?_⟩
    exact fun w hw ↦ Or.inl (mem_iUnion₂.mpr ⟨x, ⟨hxa, hxb⟩, hw⟩)
  have hCball (i) (x : Z) {w : V} (hw : w ∈ C i)
      (hwB : w ∈ closedBall x.1 (r x)) :
      (x = a i ∨ x = b i) ∧
        ∃ z, dist z x.1 = r x ∧ w ∈ segment ℝ x.1 z ∧ z ∈ (P i).toSet := by
    by_cases ha : x = a i
    · subst x
      exact ⟨Or.inl rfl, za i, hza i, hCa i ▸ ⟨hw, hwB⟩, hzaP i⟩
    by_cases hb : x = b i
    · subst x
      exact ⟨Or.inr rfl, zb i, hzb i, hCb i ▸ ⟨hw, hwB⟩, hzbP i⟩
    exact ((hCavoid i x ha hb).notMem_of_mem_left hw hwB).elim
  have hCoutside (i) {w : V} (hw : w ∈ C i)
      (hout : ∀ x : Z, w ∉ closedBall x.1 (r x)) : w ∈ (P i).toSet := by
    refine hCmid i ⟨hw, ?_⟩
    exact fun h ↦ h.elim (fun ha ↦ hout _ (ball_subset_closedBall ha))
      (fun hb ↦ hout _ (ball_subset_closedBall hb))
  refine ⟨C, hs, hpoly, ?_, ?_, ?_⟩
  · intro i
    apply subset_antisymm
    · rintro w ⟨hwC, hwZ⟩
      exact ((hCball i ⟨w, hwZ⟩ hwC (mem_closedBall_self (hpos _).le)).1).imp
        (congrArg Subtype.val) (congrArg Subtype.val)
    · rintro w (rfl | rfl)
      · exact ⟨(hs i).left_mem, (a i).2⟩
      · exact ⟨(hs i).right_mem, (b i).2⟩
  · intro i j hij w hw
    by_cases hball : ∃ x : Z, w ∈ closedBall x.1 (r x)
    · obtain ⟨x, hx⟩ := hball
      obtain ⟨-, zi, hzi, hwi, hziP⟩ := hCball i x hw.1 hx
      obtain ⟨-, zj, hzj, hwj, hzjP⟩ := hCball j x hw.2 hx
      have hzne : zi ≠ zj := fun heq ↦
        (hPdisj hij).notMem_of_mem_left hziP (heq ▸ hzjP)
      exact (eq_center_of_mem_two_radii (dist_pos.mp (hzi ▸ hpos x))
        (hzj.trans hzi.symm) hzne hwi hwj) ▸ x.2
    · push Not at hball
      exact ((hPdisj hij).notMem_of_mem_left
        (hCoutside i hw.1 hball) (hCoutside j hw.2 hball)).elim
  · intro i
    apply Subset.trans (b := thickening ε (range (F i)))
    · intro w hwC
      obtain (hwa | hwb) | hwP := hCcover i hwC
      · exact mem_thickening_iff.mpr ⟨(a i).1, (F i).source_mem_range,
          (mem_ball.mp hwa).trans (hsmall _)⟩
      · exact mem_thickening_iff.mpr ⟨(b i).1, (F i).target_mem_range,
          (mem_ball.mp hwb).trans (hsmall _)⟩
      · exact hPnear i hwP
    · exact (thickening_mono (hεδ i).le _).trans (hδU i)

/-- A finite family of primitive links meeting only at specified vertices admits polygonal
primitive replacements in prescribed open neighborhoods. Loops remain primitive loops. -/
theorem exists_polygonal_primitiveLink_family {ι : Type*} [Finite ι]
    {Z : Set V} [Finite Z] {a b : ι → Z} {L : ι → Set V}
    (hL : ∀ i, IsPrimitiveLink (L i) (a i).1 (b i).1)
    (hLV : ∀ i, L i ∩ Z ⊆ {(a i).1, (b i).1})
    (hLL : Pairwise fun i j ↦ L i ∩ L j ⊆ Z)
    (U : ι → Set V) (hU : ∀ i, IsOpen (U i)) (hLU : ∀ i, L i ⊆ U i) :
    ∃ M : ι → Set V, (∀ i, IsPrimitiveLink (M i) (a i).1 (b i).1) ∧
      (∀ i, IsSegmentFigure (M i)) ∧
      (∀ i, M i ∩ Z = {(a i).1, (b i).1}) ∧
      (Pairwise fun i j ↦ M i ∩ M j ⊆ Z) ∧ ∀ i, M i ⊆ U i := by
  classical
  choose m hm using fun i ↦ (hL i).diff_endpoints_nonempty
  have hmZ (i) : m i ∉ Z := fun h ↦ (hm i).2 (hLV i ⟨(hm i).1, h⟩)
  have hma (i) : m i ≠ (a i).1 := fun h ↦ hmZ i (h ▸ (a i).2)
  have hmb (i) : m i ≠ (b i).1 := fun h ↦ hmZ i (h ▸ (b i).2)
  let A (i) := (hL i).splitLeft (m i)
  let B (i) := (hL i).splitRight (m i)
  have hA (i) : IsPrimitiveLink (A i) (a i).1 (m i) :=
    (hL i).isPrimitiveLink_splitLeft (hm i).1 (hma i)
  have hB (i) : IsPrimitiveLink (B i) (m i) (b i).1 :=
    (hL i).isPrimitiveLink_splitRight (hm i).1 (hmb i)
  have hinter (i) : A i ∩ B i = {m i} ∪ ({(a i).1} ∩ {(b i).1}) :=
    (hL i).splitLeft_inter_splitRight (hm i).1
  have howner {i j} (h : m j ∈ L i) : i = j := by
    by_contra hij
    exact hmZ j (hLL hij ⟨h, (hm j).1⟩)
  have hminj : Injective m := fun i j h ↦ howner (h ▸ (hm i).1)
  let Z' := Z ∪ range m
  have : Finite Z' := ((toFinite Z).union (finite_range m)).to_subtype
  let c : ι × Bool → Z'
    | (i, false) => ⟨(a i).1, Or.inl (a i).2⟩
    | (i, true) => ⟨m i, Or.inr (mem_range_self i)⟩
  let d : ι × Bool → Z'
    | (i, false) => ⟨m i, Or.inr (mem_range_self i)⟩
    | (i, true) => ⟨(b i).1, Or.inl (b i).2⟩
  let K : ι × Bool → Set V | (i, false) => A i | (i, true) => B i
  have hK (j) : IsPrimitiveLink (K j) (c j).1 (d j).1 := by
    obtain ⟨i, q⟩ := j
    cases q
    · exact hA i
    · exact hB i
  have hKsub (j) : K j ⊆ L j.1 := by
    obtain ⟨i, q⟩ := j
    cases q
    · exact (hL i).splitLeft_subset (m i)
    · exact (hL i).splitRight_subset (m i)
  have hKV (j) : K j ∩ Z' ⊆ {(c j).1, (d j).1} := by
    rintro z ⟨hz, hzZ | ⟨i, rfl⟩⟩
    · have hzends := hLV j.1 ⟨hKsub j hz, hzZ⟩
      obtain ⟨i, q⟩ := j
      cases q
      · change z ∈ A i at hz
        change z ∈ ({(a i).1, m i} : Set V)
        rcases hzends with rfl | rfl
        · exact Or.inl rfl
        · have hb := (hinter i).subset ⟨hz, (hB i).right_mem⟩
          simp only [mem_union, mem_singleton_iff, mem_inter_iff] at hb
          exact Or.inl (hb.resolve_left (hmb i).symm).1
      · change z ∈ B i at hz
        change z ∈ ({m i, (b i).1} : Set V)
        rcases hzends with rfl | rfl
        · have ha := (hinter i).subset ⟨(hA i).left_mem, hz⟩
          simp only [mem_union, mem_singleton_iff, mem_inter_iff] at ha
          exact Or.inr (ha.resolve_left (hma i).symm).2
        · exact Or.inr rfl
    · have heq : j.1 = i := howner (hKsub j hz)
      obtain ⟨j, q⟩ := j
      dsimp at heq
      subst i
      cases q <;> simp [c, d]
  have hKK : Pairwise fun i j ↦ K i ∩ K j ⊆ Z' := by
    intro i j hij z hz
    by_cases heq : i.1 = j.1
    · obtain ⟨i, q⟩ := i
      obtain ⟨j, q'⟩ := j
      dsimp at heq
      subst j
      have hab : A i ∩ B i ⊆ Z' := by
        rw [hinter i]
        rintro w (rfl | ⟨rfl, _⟩)
        · exact Or.inr (mem_range_self i)
        · exact Or.inl (a i).2
      cases q <;> cases q'
      · exact (hij rfl).elim
      · exact hab hz
      · exact hab ⟨hz.2, hz.1⟩
      · exact (hij rfl).elim
    · exact Or.inl (hLL heq ⟨hKsub i hz.1, hKsub j hz.2⟩)
  choose F hF hrange using hK
  obtain ⟨C, hC, hpoly, hCV, hCC, hCU⟩ := exists_polygonal_arc_family F
    (fun i ↦ by simpa only [hrange] using hKV i)
    (fun i j hij ↦ by simpa only [hrange] using hKK hij)
    (by rintro ⟨i, q⟩ h; have heq := congrArg Subtype.val h
        cases q
        · exact hma i heq.symm
        · exact hmb i heq)
    (fun i ↦ U i.1) (fun i ↦ hU i.1)
    (fun i ↦ by rw [hrange]; exact (hKsub i).trans (hLU i.1))
  have hmid {i : ι × Bool} {z} (hz : z ∈ C i) (hzV : z ∈ Z') (hzZ : z ∉ Z) :
      z = m i.1 := by
    have he := (hCV i).subset ⟨hz, hzV⟩
    obtain ⟨i, q⟩ := i
    cases q
    · exact he.resolve_left (fun h ↦ hzZ (h ▸ (a i).2))
    · exact he.resolve_right (fun h ↦ hzZ (h ▸ (b i).2))
  have hM (i) : IsPrimitiveLink (C (i, false) ∪ C (i, true)) (a i).1 (b i).1 := by
    apply (hC (i, false)).union_of_inter_subset (hC (i, true)) (hma i).symm (hmb i)
    intro z hz
    have hzV := hCC (by simp) hz
    exact ⟨(hCV (i, false)).subset ⟨hz.1, hzV⟩, (hCV (i, true)).subset ⟨hz.2, hzV⟩⟩
  refine ⟨fun i ↦ C (i, false) ∪ C (i, true), hM,
    fun i ↦ (hpoly (i, false)).union (hpoly (i, true)), ?_, ?_,
    fun i ↦ union_subset (hCU (i, false)) (hCU (i, true))⟩
  · intro i
    apply Subset.antisymm
    · rintro z ⟨hz | hz, hzZ⟩
      · have he := (hCV (i, false)).subset ⟨hz, Or.inl hzZ⟩
        change z = (a i).1 ∨ z = m i at he
        exact Or.inl (he.resolve_right (fun h ↦ hmZ i (h ▸ hzZ)))
      · have he := (hCV (i, true)).subset ⟨hz, Or.inl hzZ⟩
        change z = m i ∨ z = (b i).1 at he
        exact Or.inr (he.resolve_left (fun h ↦ hmZ i (h ▸ hzZ)))
    · rintro z (rfl | rfl)
      · exact ⟨(hM i).left_mem, (a i).2⟩
      · exact ⟨(hM i).right_mem, (b i).2⟩
  · intro i j hij z hz
    by_contra hzZ
    have hcross (q q') (hi : z ∈ C (i, q)) (hj : z ∈ C (j, q')) : False := by
      have hzV := hCC (fun h ↦ hij (congrArg Prod.fst h)) ⟨hi, hj⟩
      exact hij (hminj ((hmid hi hzV hzZ).symm.trans (hmid hj hzV hzZ)))
    exact hz.1.elim (fun hi ↦ hz.2.elim (hcross false false hi) (hcross false true hi))
      (fun hi ↦ hz.2.elim (hcross true false hi) (hcross true true hi))

end
