module

public import Matroid.ForMathlib.Analysis.Convex.RadialPoint
public import Matroid.ForMathlib.Analysis.Convex.Segment
public import Matroid.ForMathlib.Geometry.PolygonalPath.Basic
public import Matroid.ForMathlib.Topology.MetricSpace

@[expose] public section

/-!
# Segment figures and the star lemma

A **segment figure** is a finite union of segments together with finitely many extra points. About
each of its points such a set is a star of finitely many straight radii — that is `exists_radius`
below, and it is all the local structure the planarity development uses.

## Why this file exists

`exists_radius` was previously stated about a `PLDrawing` of a finite graph. In its proof the
drawing occurred exactly twice, both times as `range D.toDrawing.vertex`, and both times only its
*finiteness* was used; everything else came from `PLDrawing.exists_finite_support`, whose conclusion
is precisely `IsSegmentFigure`. So the star lemma is a fact about finite unions of segments, and
stating it about a drawing put it out of reach of every caller that has such a union but no graph —
notably the θ-curve of Status.md 3.9, which is three polygonal arcs and no drawing.

Nothing here mentions a graph, so by Kuratowski `Decisions.md` D14 it lives in `ForMathlib`.

## The radius count

`exists_radius` produces a `Y` whose radii cover the figure near `p`, but says nothing about
`Y.card`. That count is what both known callers actually need — `Y.card = G.degree v` at a vertex of
a drawing, `Y.card = 3` at an endpoint of a θ-curve — and it is genuinely separate content, because
`Y` counts *directions* out of `p`, not segment ends: two ends positively parallel to each other
contribute one radius between them.

`card_radii_le_of_cover` and `le_card_radii_of_pairwise` are the two bounds, in the form both
callers instantiate. The primitive underneath them is
`exists_segment_subset_inter_of_radialPoint_eq` (`Convex/RadialPoint.lean`): two ends in the same
direction share a nondegenerate initial segment, which is what turns "these two pieces meet only at
`p`" into "these two pieces point in different directions".

## What deliberately lives elsewhere

Two facts this file used to carry have no `IsSegmentFigure` in their statements, so nobody needing
them would think to look here:

* `exists_pos_le_dist_of_notMem` — a point off a closed set stays a positive distance from all of
  it. Pure metric space, and `Graph/Planarity/PLReduction.lean` reinvents it; now in
  `ForMathlib/Topology/MetricSpace.lean`, generalised from normed groups to `PseudoMetricSpace`.
* `PolygonalPath.exists_ball_inter_subset_firstSegment` — now in `PolygonalPath/Basic.lean`, whose
  `section Metric` exists for it. It is what supplies `hUz` for `card_radii_le_of_cover` when the
  pieces are polygonal arcs.

A bundled `IsStar p ρ Y T` for the recurring `(hY, hstar)` pair was considered and rejected: the
counting lemmas below are deliberately stated about *any* `Y` satisfying the star equation, and
pinning `Y` down is what defeated the earlier attempt on `PLDrawing.exists_radius_vertex`.

## Main definitions

* `IsSegmentFigure`

## Main statements

* `IsSegmentFigure.exists_radius` : the star lemma, over any real normed space.
* `le_card_radii_of_pairwise`, `card_radii_le_of_cover` : the radius count.
-/

open Set Metric

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {T T₁ T₂ : Set V} {p : V} {ρ : ℝ}
  {Y : Finset V}

/-- `T` is a **segment figure**: finitely many segments together with finitely many extra points.

The extra points are kept as a separate finite set rather than folded into degenerate segments
`segment ℝ x x = {x}`. That is deliberate: `exists_radius` builds its radii from where each segment
*through* `p` crosses `sphere p ρ`, and a degenerate segment at `p` has no such crossing, so folding
them in would add a case to that construction and force a side condition on `↑Y ⊆ sphere p ρ`. In
this shape the hypothesis matches `PLDrawing.exists_finite_support` term for term. -/
def IsSegmentFigure (T : Set V) : Prop :=
  ∃ (F : Set V) (S : Set (V × V)), F.Finite ∧ S.Finite ∧ T = F ∪ ⋃ s ∈ S, segment ℝ s.1 s.2

/-! ### The star lemma -/

/-- **The star lemma.** About each of its points, a segment figure meets a small enough closed ball
in a union of straight radii, one for each direction in which the figure leaves the point.

No hypothesis on the ambient space beyond a norm: the radius is chosen below the distance from `p`
to the finitely many segments not touching it, below the length of each segment ending at `p`, and
below the distance to the endpoints of a segment through `p`.

`Y` may be empty — at an isolated point of the figure the star is `{p}` — which is why the equality
is stated with `{p} ∪ ⋃ …` rather than assuming `Y.Nonempty`. -/
theorem IsSegmentFigure.exists_radius (hT : IsSegmentFigure T) (hp : p ∈ T) :
    ∃ ρ > 0, ∃ Y : Finset V, ↑Y ⊆ sphere p ρ ∧
      closedBall p ρ ∩ T = {p} ∪ ⋃ y ∈ Y, segment ℝ p y := by
  classical
  obtain ⟨F, S0, hFfin, hSfin, hsupp⟩ := hT
  let Sp : Set (V × V) := {s ∈ S0 | p ∈ segment ℝ s.1 s.2}
  let Srest : Set (V × V) := {s ∈ S0 | p ∉ segment ℝ s.1 s.2}
  have hSpfin : Sp.Finite := hSfin.subset fun _ h ↦ h.1
  have hSrestfin : Srest.Finite := hSfin.subset fun _ h ↦ h.1
  let K : Set V := (F \ {p}) ∪ ⋃ s ∈ Srest, segment ℝ s.1 s.2
  have hKcompact : IsCompact K := ((hFfin.subset sdiff_subset).isCompact).union
    (hSrestfin.isCompact_biUnion fun _ _ ↦ isCompact_segment _ _)
  have hKclosed : IsClosed K := hKcompact.isClosed
  have hpK : p ∉ K := by
    refine not_or.mpr ⟨fun h ↦ h.2 rfl, fun hp' ↦ ?_⟩
    obtain ⟨s, hs, hseg⟩ := mem_iUnion₂.mp hp'
    exact hs.2 hseg
  obtain ⟨δ, hδpos, hδle⟩ := exists_pos_le_dist_of_notMem hKclosed (by simpa using hpK)
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
    rw [dist_comm] at hle
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
      segment_subset_segment_right (radialPoint_mem_segment p z hρpos.le (hρ_le_end z hzend))
    rw [hsupp]
    exact Or.inr (mem_iUnion₂.mpr ⟨s, hsSp.1, hsub (h1 hxseg)⟩)

/-! ### Recognising segment figures -/

/- Route: take `F := ∅` and `S := {(x, y)}`; `Set.finite_singleton`, `Set.finite_empty`, then
`simp` for the union. -/
@[grind .]
theorem isSegmentFigure_segment (x y : V) : IsSegmentFigure (segment ℝ x y) :=
  ⟨∅, {(x, y)}, finite_empty, finite_singleton _, by simp⟩

/- Route: take `S := ∅`. -/
@[grind .]
theorem IsSegmentFigure.of_finite (hF : T.Finite) : IsSegmentFigure T :=
  ⟨T, ∅, hF, finite_empty, by simp⟩

/- Route: destructure both, take `F₁ ∪ F₂` and `S₁ ∪ S₂`; `Set.Finite.union`, then
`Set.biUnion_union` and `union_assoc`/`union_comm` to reassociate. -/
@[grind .]
theorem IsSegmentFigure.union (h₁ : IsSegmentFigure T₁) (h₂ : IsSegmentFigure T₂) :
    IsSegmentFigure (T₁ ∪ T₂) := by
  obtain ⟨F₁, S₁, hF₁, hS₁, rfl⟩ := h₁
  obtain ⟨F₂, S₂, hF₂, hS₂, rfl⟩ := h₂
  refine ⟨F₁ ∪ F₂, S₁ ∪ S₂, hF₁.union hF₂, hS₁.union hS₂, ?_⟩
  rw [biUnion_union]
  ac_rfl

/- Route: `choose F S hFfin hSfin hEq using hU`, then take `⋃ i, F i` and `⋃ i, S i`, both finite by
`Set.finite_iUnion` (this is where `[Finite ι]` is used). Finish with `Set.iUnion_union_distrib` and
`Set.biUnion_iUnion` to reassociate.

Not an induction over the index type: `ι` is a `Finite` type, not a finite `Set`, so
`Set.Finite.induction_on` does not apply and `IsSegmentFigure.union` is not needed here. -/
@[grind .]
theorem IsSegmentFigure.iUnion {ι : Type*} [Finite ι] {U : ι → Set V}
    (hU : ∀ i, IsSegmentFigure (U i)) : IsSegmentFigure (⋃ i, U i) := by
  choose F S hFfin hSfin hEq using hU
  refine ⟨⋃ i, F i, ⋃ i, S i, finite_iUnion hFfin, finite_iUnion hSfin, ?_⟩
  simp_rw [hEq, iUnion_union_distrib, biUnion_iUnion]

/-- A polygonal path traces a segment figure. This is what lets Status.md §3.9 apply the star lemma
to a θ-curve, which is three arcs and no drawing.

Route: `PolygonalPath.toSet_eq_insert_biUnion` (`PolygonalPath/Basic.lean:588`) gives
`P.toSet = insert y (⋃ s ∈ P.edges, segment ℝ s.1 s.2)`. Take `F := {y}` and
`S := {s | s ∈ P.edges}`, finite by `List.finite_toSet`. -/
@[grind .]
theorem PolygonalPath.isSegmentFigure_toSet {x y : V} (P : PolygonalPath x y) :
    IsSegmentFigure P.toSet := by
  refine ⟨{y}, {s | s ∈ P.edges}, finite_singleton _, P.edges.finite_toSet, ?_⟩
  rw [PolygonalPath.toSet_eq_insert_biUnion]
  rfl

/-! ### Shrinking the star

`exists_radius` hands the caller a `ρ` it did not choose, but both counting arguments below need `ρ`
small enough for some caller-side condition — small enough that `b` is outside the ball, that a
polygonal arc has not re-entered it, that two cells at a vertex have separated. So the star has to
be shrinkable, and the radius count has to be invariant under shrinking. **Callers should shrink
first and count second.** -/

/-- The star survives shrinking the radius, with the same number of radii.

Without this the counting lemmas below are unusable: their hypotheses on the pieces `U i` hold only
for small `ρ`, and `exists_radius` does not let the caller pick `ρ`.

Route: take `Y' := Y.image (radialPoint p · ρ')`. The equality is `hstar` intersected with
`closedBall p ρ'`, using `segment_inter_closedBall_eq_radial` (`RadialPoint.lean:110`) on each
radius to cut it at the smaller radius. `↑Y' ⊆ sphere p ρ'` is `mem_sphere_radialPoint`
(`RadialPoint.lean:136`). For `Y'.card = Y.card` use `Finset.card_image_of_injOn` and
`radialPoint_eq_iff_pos_parallel` (`RadialPoint.lean:243`): two distinct points of `sphere p ρ` are
never positively parallel, since `a - p = t • (b - p)` with `‖a - p‖ = ‖b - p‖ = ρ` and `0 < t`
forces `t = 1`. -/
theorem exists_radius_of_le {ρ' : ℝ} (hρ : 0 < ρ) (hY : ↑Y ⊆ sphere p ρ)
    (hstar : closedBall p ρ ∩ T = {p} ∪ ⋃ y ∈ Y, segment ℝ p y)
    (hρ' : 0 < ρ') (hle : ρ' ≤ ρ) :
    ∃ Y' : Finset V, ↑Y' ⊆ sphere p ρ' ∧ Y'.card = Y.card ∧
      closedBall p ρ' ∩ T = {p} ∪ ⋃ y ∈ Y', segment ℝ p y := by
  classical
  have hYne (y : V) (hy : y ∈ Y) : y ≠ p := ne_of_mem_sphere (hY hy) hρ.ne'
  have hYdist (y : V) (hy : y ∈ Y) : dist p y = ρ := mem_sphere'.mp (hY hy)
  let Y' : Finset V := Y.image (radialPoint p · ρ')
  have hY'sphere : ↑Y' ⊆ sphere p ρ' := by
    intro y hy
    obtain ⟨z, hzY, rfl⟩ := Finset.mem_image.mp (show y ∈ Y' from hy)
    exact mem_sphere_radialPoint p z hρ'.le (hYne z hzY)
  have hcard : Y'.card = Y.card := by
    refine Finset.card_image_of_injOn ?_
    intro a haY b hbY heq
    obtain ⟨t, htpos, hpar⟩ :=
      (radialPoint_eq_iff_pos_parallel p a b hρ' (hYne a haY) (hYne b hbY)).mp heq
    have hna : ‖a - p‖ = ρ := mem_sphere_iff_norm.mp (hY haY)
    have hnb : ‖b - p‖ = ρ := mem_sphere_iff_norm.mp (hY hbY)
    have ht1 : t = 1 := by
      have : ρ = t * ρ := by
        calc
          ρ = ‖a - p‖ := hna.symm
          _ = ‖t • (b - p)‖ := by rw [hpar]
          _ = |t| * ‖b - p‖ := by rw [norm_smul, Real.norm_eq_abs]
          _ = t * ρ := by rw [abs_of_pos htpos, hnb]
      exact (mul_eq_right₀ hρ.ne').mp this.symm
    have hab : a - p = b - p := by simpa [ht1, one_smul] using hpar
    exact sub_left_injective hab
  refine ⟨Y', hY'sphere, hcard, subset_antisymm ?_ ?_⟩
  · intro x ⟨hxball', hxT⟩
    have hxball : x ∈ closedBall p ρ :=
      closedBall_subset_closedBall hle hxball'
    have hxstar : x ∈ ({p} : Set V) ∪ ⋃ y ∈ Y, segment ℝ p y := by
      rw [← hstar]; exact ⟨hxball, hxT⟩
    rcases hxstar with hxp | hxrad
    · exact Or.inl (mem_singleton_iff.mp hxp)
    · obtain ⟨y, hyY, hxseg⟩ := mem_iUnion₂.mp hxrad
      have hyle : ρ' ≤ dist p y := by
        rw [hYdist y hyY]; exact hle
      have hx' : x ∈ closedBall p ρ' ∩ segment ℝ p y := ⟨hxball', hxseg⟩
      rw [segment_inter_closedBall_eq_radial p y hρ' (hYne y hyY) hyle] at hx'
      exact Or.inr (mem_iUnion₂.mpr
        ⟨radialPoint p y ρ', Finset.mem_image_of_mem _ hyY, hx'⟩)
  · intro x hx
    rcases hx with hxp | hx
    · rw [mem_singleton_iff.mp hxp]
      refine ⟨mem_closedBall_self hρ'.le, ?_⟩
      have hpT : p ∈ closedBall p ρ ∩ T := by
        rw [hstar]; exact Or.inl rfl
      exact hpT.2
    · obtain ⟨y', hy'Y', hxseg⟩ := mem_iUnion₂.mp hx
      obtain ⟨y, hyY, rfl⟩ := Finset.mem_image.mp hy'Y'
      have hyle : ρ' ≤ dist p y := by rw [hYdist y hyY]; exact hle
      have hsub : segment ℝ p (radialPoint p y ρ') ⊆ segment ℝ p y :=
        segment_subset_segment_right (radialPoint_mem_segment p y hρ'.le hyle)
      have hxY : x ∈ ⋃ y ∈ Y, segment ℝ p y :=
        mem_iUnion₂.mpr ⟨y, hyY, hsub hxseg⟩
      have hxstar : x ∈ closedBall p ρ ∩ T := by
        rw [hstar]; exact Or.inr hxY
      refine ⟨?_, hxstar.2⟩
      exact (convex_closedBall p ρ').segment_subset (mem_closedBall_self hρ'.le)
        (sphere_subset_closedBall (hY'sphere (Finset.mem_image_of_mem _ hyY))) hxseg

/-! ### Counting the radii

`exists_radius` says nothing about `Y.card`, and that count is what callers need. `Y` counts
*directions* out of `p`: by `radialPoint_eq_iff_pos_parallel` (`RadialPoint.lean:243`) two ends give
the same radius exactly when they are positively parallel. The two bounds below are stated in the
form both known callers instantiate — a family `U` of pieces of `T` meeting only at `p`.

Both are stated about *any* `Y` satisfying the star equation, so the caller never has to look inside
the `Y` that `exists_radius` produced. Pinning `Y` down is what defeated the earlier attempt on
`PLDrawing.exists_radius_vertex`. -/

/-- **Counting radii from below.** If `T` contains pieces `U i` that pairwise meet only at `p`, each
leaving `p` along some nondegenerate segment, then there are at least that many radii.

Route: for each `i` pick `z i ≠ p` with `segment ℝ p (z i) ⊆ U i`. Put a point of
`segment p (z i) \ {p}` into `closedBall ∩ T` via `radialPoint` at `min ρ (dist p z)`, read a radius
off `hstar`, and inject by shared initial segments on equal images. -/
theorem le_card_radii_of_pairwise {ι : Type*} [Fintype ι] {U : ι → Set V} (hρ : 0 < ρ)
    (hY : ↑Y ⊆ sphere p ρ)
    (hstar : closedBall p ρ ∩ T = {p} ∪ ⋃ y ∈ Y, segment ℝ p y)
    (hUT : ∀ i, U i ⊆ T) (hUp : ∀ i, ∃ z ≠ p, segment ℝ p z ⊆ U i)
    (hmeet : ∀ i j, i ≠ j → U i ∩ U j ⊆ {p}) :
    Fintype.card ι ≤ Y.card := by
  classical
  choose z hzne hseg using hUp
  let r (i : ι) : ℝ := min ρ (dist p (z i))
  have hrpos (i : ι) : 0 < r i := lt_min hρ (dist_pos.mpr (hzne i).symm)
  have hr_le_z (i : ι) : r i ≤ dist p (z i) := min_le_right _ _
  have hr_le_ρ (i : ι) : r i ≤ ρ := min_le_left _ _
  let w (i : ι) : V := radialPoint p (z i) (r i)
  have hwne (i : ι) : w i ≠ p :=
    ne_of_mem_sphere (mem_sphere_radialPoint p (z i) (hrpos i).le (hzne i)) (hrpos i).ne'
  have hwseg (i : ι) : w i ∈ segment ℝ p (z i) :=
    radialPoint_mem_segment p (z i) (hrpos i).le (hr_le_z i)
  have hwU (i : ι) : w i ∈ U i := hseg i (hwseg i)
  have hwball (i : ι) : w i ∈ closedBall p ρ := by
    have hdist : dist (w i) p = r i := by
      dsimp [w]
      exact dist_radialPoint p (z i) (hrpos i).le (hzne i)
    exact mem_closedBall.mpr (hdist.trans_le (hr_le_ρ i))
  have hwY (i : ι) : ∃ y ∈ Y, w i ∈ segment ℝ p y := by
    have hx : w i ∈ closedBall p ρ ∩ T := ⟨hwball i, hUT i (hwU i)⟩
    rw [hstar] at hx
    rcases hx with hwp | hwrad
    · exact (hwne i hwp).elim
    · obtain ⟨y, hy, hwy⟩ := mem_iUnion₂.mp hwrad
      exact ⟨y, hy, hwy⟩
  choose f hfY hwf using hwY
  have hinj : Function.Injective f := by
    intro i j hfij
    by_contra hne
    have hyi := hwf i
    have hyj : w j ∈ segment ℝ p (f i) := hfij ▸ hwf j
    obtain ⟨ti, ⟨hti0, _⟩, hwi⟩ :=
      (segment_eq_image_lineMap (𝕜 := ℝ) p (f i)).symm ▸ hyi
    obtain ⟨tj, ⟨htj0, _⟩, hwj⟩ :=
      (segment_eq_image_lineMap (𝕜 := ℝ) p (f i)).symm ▸ hyj
    have hti_pos : 0 < ti :=
      lt_of_le_of_ne hti0 fun h0 ↦
        hwne i (by rw [← hwi, ← h0, AffineMap.lineMap_apply_zero])
    have htj_pos : 0 < tj :=
      lt_of_le_of_ne htj0 fun h0 ↦
        hwne j (by rw [← hwj, ← h0, AffineMap.lineMap_apply_zero])
    let t : ℝ := min ti tj
    have htpos : 0 < t := lt_min hti_pos htj_pos
    let a : V := AffineMap.lineMap p (f i) t
    have ha_ne : a ≠ p := by
      intro ha
      rcases AffineMap.lineMap_eq_left_iff.mp ha with hfp | ht0
      · exact ne_of_mem_sphere (hY (hfY i)) hρ.ne' hfp.symm
      · exact htpos.ne' ht0
    have ha_wi : a ∈ segment ℝ p (w i) := by
      rw [← hwi, segment_eq_image_lineMap]
      refine ⟨t / ti, ⟨div_nonneg htpos.le hti_pos.le,
        div_le_one_of_le₀ (min_le_left ti tj) hti_pos.le⟩, ?_⟩
      rw [AffineMap.lineMap_lineMap_right, div_mul_cancel₀ _ hti_pos.ne']
    have ha_wj : a ∈ segment ℝ p (w j) := by
      rw [← hwj, segment_eq_image_lineMap]
      refine ⟨t / tj, ⟨div_nonneg htpos.le htj_pos.le,
        div_le_one_of_le₀ (min_le_right ti tj) htj_pos.le⟩, ?_⟩
      rw [AffineMap.lineMap_lineMap_right, div_mul_cancel₀ _ htj_pos.ne']
    have ha_Ui : a ∈ U i :=
      hseg i <| segment_subset_segment_right (hwseg i) ha_wi
    have ha_Uj : a ∈ U j :=
      hseg j <| segment_subset_segment_right (hwseg j) ha_wj
    exact ha_ne (hmeet i j hne ⟨ha_Ui, ha_Uj⟩)
  have himg : Finset.univ.image f ⊆ Y := by
    intro y hy
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hy
    exact hfY i
  calc
    Fintype.card ι = Finset.univ.card := rfl
    _ = (Finset.univ.image f).card := (Finset.card_image_of_injective _ hinj).symm
    _ ≤ Y.card := Finset.card_le_card himg

/-- **Counting radii from above.** If the pieces `U i` cover `T` near `p` and each leaves `p` in a
single direction, then there are at most that many radii.

"Leaves in a single direction" is `U i ∩ closedBall p ρ ⊆ segment ℝ p (z i)`: near `p` the piece is
contained in one radius.

**`hUz` is only true for small `ρ`** — a polygonal arc can leave the ball and come back, and two
cells at a vertex separate only eventually. So shrink first with `exists_radius_of_le`, which keeps
the count, and apply this at the smaller radius.
`PolygonalPath.exists_ball_inter_subset_firstSegment`
supplies the radius for an arc.

Route: every `y ∈ Y` satisfies `segment ℝ p y ⊆ T ∩ closedBall p ρ` by `hstar`, so `y` lies in some
`U i`, hence on `segment ℝ p (z i)`; since `y ∈ sphere p ρ` and `z i ≠ p`, that forces
`y = radialPoint p (z i) ρ` (`segment_inter_closedBall_eq_radial` pins the point of a radius at
distance exactly `ρ`). So `Y ⊆ image (fun i ↦ radialPoint p (z i) ρ)`, and
`Finset.card_le_card` with `Finset.card_image_le` finishes. -/
theorem card_radii_le_of_cover {ι : Type*} [Fintype ι] {U : ι → Set V} {z : ι → V} (hρ : 0 < ρ)
    (hY : ↑Y ⊆ sphere p ρ)
    (hstar : closedBall p ρ ∩ T = {p} ∪ ⋃ y ∈ Y, segment ℝ p y)
    (hcover : T ∩ closedBall p ρ ⊆ {p} ∪ ⋃ i, U i)
    (hzne : ∀ i, z i ≠ p) (hUz : ∀ i, U i ∩ closedBall p ρ ⊆ segment ℝ p (z i)) :
    Y.card ≤ Fintype.card ι := by
  classical
  let g : ι → V := fun i ↦ radialPoint p (z i) ρ
  have hYsub : Y ⊆ Finset.univ.image g := by
    intro y hyY
    have hysph : y ∈ sphere p ρ := hY hyY
    have hyball : y ∈ closedBall p ρ := sphere_subset_closedBall hysph
    have hyne : y ≠ p := ne_of_mem_sphere hysph hρ.ne'
    have hyT : y ∈ T := by
      have : y ∈ closedBall p ρ ∩ T := by
        rw [hstar]
        exact Or.inr (mem_iUnion₂.mpr ⟨y, hyY, right_mem_segment _ _ _⟩)
      exact this.2
    have hycover : y ∈ ({p} : Set V) ∪ ⋃ i, U i :=
      hcover ⟨hyT, hyball⟩
    rcases hycover with hyeq | hyU
    · exact (hyne hyeq).elim
    · obtain ⟨i, hyUi⟩ := mem_iUnion.mp hyU
      have hyseg : y ∈ segment ℝ p (z i) := hUz i ⟨hyUi, hyball⟩
      obtain ⟨t, ⟨ht0, ht1⟩, hyline⟩ :=
        (segment_eq_image_lineMap (𝕜 := ℝ) p (z i)).symm ▸ hyseg
      have hydist : dist y p = ρ := mem_sphere.mp hysph
      have hydist' : dist (AffineMap.lineMap p (z i) t) p = ρ := by
        rw [hyline]; exact hydist
      rw [dist_lineMap_left_of_nonneg p (z i) ht0] at hydist'
      have hle : ρ ≤ dist p (z i) := by
        calc
          ρ = t * dist p (z i) := hydist'.symm
          _ ≤ 1 * dist p (z i) := mul_le_mul_of_nonneg_right ht1 dist_nonneg
          _ = dist p (z i) := one_mul _
      have hrad : y ∈ segment ℝ p (radialPoint p (z i) ρ) := by
        have : y ∈ closedBall p ρ ∩ segment ℝ p (z i) := ⟨hyball, hyseg⟩
        rwa [segment_inter_closedBall_eq_radial p (z i) hρ (hzne i) hle] at this
      have hyeq : y = radialPoint p (z i) ρ :=
        eq_of_mem_segment_of_mem_sphere p hρ
          (mem_sphere_radialPoint p (z i) hρ.le (hzne i)) hrad hysph
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hyeq.symm⟩
  calc
    Y.card ≤ (Finset.univ.image g).card := Finset.card_le_card hYsub
    _ ≤ Finset.univ.card := Finset.card_image_le
    _ = Fintype.card ι := Finset.card_univ

/-- **The radius endpoints are exactly the sphere section.** Given a star at `p` for any set `S`,
the finset `Y` is determined: it is `sphere p ρ ∩ S`.

This is what makes `Y` canonical, and hence what makes the two counting bounds above statements
about `S` rather than about a particular witness. Nothing about drawings or graphs is involved —
`S` is an arbitrary set, and the star equation is the only hypothesis. -/
theorem coe_eq_sphere_inter_of_star {S : Set V} (hρ : 0 < ρ) (hYsph : ↑Y ⊆ sphere p ρ)
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
    · exact absurd (mem_singleton_iff.mp hy') (ne_of_mem_sphere hysph hρ.ne')
    · obtain ⟨y', hy'Y, hyseg⟩ := mem_iUnion₂.mp hy'
      rw [eq_of_mem_segment_of_mem_sphere p hρ (hYsph hy'Y) hyseg hysph]
      simpa using hy'Y

end
