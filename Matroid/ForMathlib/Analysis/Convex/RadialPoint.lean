module

public import Matroid.ForMathlib.Analysis.Convex.Segment
public import Mathlib.Analysis.Normed.Affine.AddTorsor

/-!
# The point at a given distance along a ray

`radialPoint p z ρ` is the point at distance `ρ` from `p` on the ray from `p` towards `z`. Its
reason to exist is `segment_inter_closedBall_eq_radial`: intersecting a segment with a closed ball
centred at one of its endpoints gives a shorter segment, and `radialPoint` names the new endpoint.

## Main statements

* `dist_radialPoint`, `mem_sphere_radialPoint` : the defining property.
* `segment_inter_closedBall_eq_radial` : truncating a segment to a ball centred at an endpoint.
* `closedBall_inter_segment_eq_two_radii` : the same for a ball centred at an interior point, where
  the result is the union of two radii.
* `radialPoint_eq_iff_pos_parallel`, `radialPoint_ne_of_mem_openSegment` : when two radii of the
  same ball coincide.
* `exists_segment_subset_inter_of_radialPoint_eq` : what coinciding buys you — two segments whose
  radii agree share a nondegenerate initial segment.

## Implementation notes

### Simp normal form

Exactly one lemma here is `@[simp]`: `norm_radialPoint_sub`, stated as
`‖radialPoint p z ρ - p‖ = ρ`.

That shape is not a matter of taste. In a normed space Mathlib normalises ball and sphere
membership to *norms* rather than to `dist` — `mem_sphere_iff_norm` and `mem_closedBall_iff_norm`
carry `@[simp high]`, outranking `mem_sphere`. The `dist`-shaped statement
`dist (radialPoint …) p` is therefore never what `simp` is looking at by the time it could apply,
and tagging `dist_radialPoint` instead leaves the goal stuck at `‖radialPoint p z ρ - p‖ = ρ`
— verified, not guessed. `dist_radialPoint` is kept untagged as the human-facing form.

"Exactly one" was re-checked when `segment_diff_ball_eq_singleton` and
`segment_radial_inter_eq_center` were added, and it still holds. Measured, by tagging both
`@[simp]` and running the goals they were written for: plain `simp` reports `made no progress`,
while `simp [*]` closes both. So the left-hand sides *do* match — what fails is discharging the side
conditions (`dist z p = ρ`, `dist z₂ p = dist z₁ p`), which live in the caller's hypotheses and
which plain `simp` does not consult. As `@[simp]` rules they would be dead weight: a match attempt
on every `segment \ ball` and `segment ∩ segment` in the library, followed by a failed discharge.
`grind` has no such problem, because it reasons from the local context. **The same two lemmas are
good `@[grind =]` rules and bad `@[simp]` ones**, and that asymmetry — not the shape of the
left-hand side — is what decides a conditional rewrite.

### What is deliberately *not* tagged

`segment_inter_closedBall_eq_radial` is the main theorem but is **not** a simp lemma. Its left-hand
side `closedBall p ρ ∩ segment ℝ p z` is built from pre-existing notions, so as a simp lemma it
would fire anywhere in the library that pattern occurs and would drag `radialPoint` — a definition
most contexts have no interest in — into unrelated goals. Introducing `radialPoint` should be a
deliberate step.

The rule of thumb used throughout this file: tag a lemma whose left-hand side is *headed by*
`radialPoint`, since it can then only fire where `radialPoint` already appears and its cost is
bounded by that. Do not tag one whose left-hand side is headed by pre-existing notions and whose
right-hand side introduces `radialPoint`.

### `grind` tags

Tagged broadly, because a `grind` rule keyed on `radialPoint` cannot fire in a goal that does not
mention `radialPoint` — so the cost is confined to callers who are already working with this API,
and under-tagging costs them far more than over-tagging costs anyone else.

Which form to use follows from *where the pattern lives*:

* `@[grind =]` for the equations — `dist_radialPoint`, `segment_inter_closedBall_eq_radial`,
  `closedBall_inter_segment_eq_two_radii`, and friends.
* `@[grind .]` where the conclusion carries `radialPoint` but the hypotheses are numeric side
  conditions — `mem_sphere_radialPoint`, `radialPoint_mem_segment`,
  `radialPoint_ne_of_mem_openSegment`. `@[grind →]` keys on *antecedents*, so it is rejected
  outright here (`failed to find patterns in the antecedents`) or, worse, keys on an over-general
  pattern like `dist p z` that fires everywhere.

Two lemmas here are keyed on their *antecedents* rather than a left-hand side, and the reason is
worth keeping. `segment_radial_inter_eq_center` states `segment ℝ p z₁ ∩ segment ℝ p z₂ = {p}`, so
`@[grind =]` reaches only a caller who has formed that intersection as a term. The callers do not:
they hold `w ∈ segment ℝ p z₁` and `w ∈ segment ℝ p z₂` separately. `eq_center_of_mem_two_radii` is
the pointwise form that reaches them, `@[grind →]`. Both are tagged; they fire in disjoint
situations.

The same lemma also shows why the statement avoids a named radius `ρ`: with `dist zᵢ p = ρ` as
hypotheses, `ρ` occurs nowhere in the left-hand side, `@[grind =]` is rejected with
`invalid pattern(s)`, and no choice of form repairs it. Spelling the shared radius as
`dist z₂ p = dist z₁ p` fixes the pattern and drops a hypothesis. See `lean/Assimilation.md` §3.

Measured, not asserted: with `grind.unusedLemmaThreshold = 10` over the reverse-reachability
closure of this file, **no lemma in it is reported** as activated-without-contribution. The
regression `example`s at the end of this file are what make that measurement possible at all — they
are the only `grind` call sites over this API — and each fails if its tag is removed. If `grind`
ever does get slow here, `radialPoint_eq_iff_pos_parallel` is the first tag to drop: it is the one
whose right-hand side introduces an existential.
-/

@[expose] public section

open Set Metric

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

@[grind =]
lemma dist_lineMap_left_of_nonneg (p z : V) {t : ℝ} (ht : 0 ≤ t) :
    dist (AffineMap.lineMap p z t) p = t * dist p z := by
  rw [dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg ht]

noncomputable def radialPoint (p z : V) (ρ : ℝ) : V :=
  AffineMap.lineMap p z (ρ / dist p z)

/-- The defining property, at the `dist` level. Oriented with the constructed point on the left,
matching `mem_sphere`, `mem_closedBall` and Mathlib's `dist_lineMap_left`.

Deliberately **not** `@[simp]`: see `norm_radialPoint_sub` for the tagged form. -/
@[grind =]
lemma dist_radialPoint (p z : V) {ρ : ℝ} (hρ : 0 ≤ ρ) (hne : z ≠ p) :
    dist (radialPoint p z ρ) p = ρ := by
  have hzpos : 0 < dist p z := dist_pos.mpr hne.symm
  rw [radialPoint, dist_lineMap_left_of_nonneg p z (div_nonneg hρ hzpos.le),
    div_mul_cancel₀ _ hzpos.ne']

/-- The defining property in `simp`-normal form.

`Mathlib` normalises ball and sphere membership in a normed space to *norms*, not to `dist`:
`mem_sphere_iff_norm` and `mem_closedBall_iff_norm` are `@[simp high]`. So a `dist`-shaped rule
loses the race in precisely the goals where it would be wanted, and this is the statement that
has to carry the `@[simp]` attribute instead. -/
@[simp, grind =]
lemma norm_radialPoint_sub (p z : V) {ρ : ℝ} (hρ : 0 ≤ ρ) (hne : z ≠ p) :
    ‖radialPoint p z ρ - p‖ = ρ := by
  rw [← dist_eq_norm]
  exact dist_radialPoint p z hρ hne

@[grind .]
lemma radialPoint_mem_segment (p z : V) {ρ : ℝ} (hρ : 0 ≤ ρ) (hle : ρ ≤ dist p z) :
    radialPoint p z ρ ∈ segment ℝ p z := by
  rw [radialPoint, segment_eq_image_lineMap]
  exact ⟨ρ / dist p z, ⟨div_nonneg hρ dist_nonneg, (div_le_one_of_le₀ hle dist_nonneg)⟩, rfl⟩

private lemma lineMap_eq_lineMap_radial (p z : V) {ρ t : ℝ} (hρ : 0 < ρ) (hne : z ≠ p) :
    AffineMap.lineMap p z t =
      AffineMap.lineMap p (radialPoint p z ρ) (t * dist p z / ρ) := by
  simp only [radialPoint, AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub, add_sub_cancel_right]
  have hcoef : t * dist p z / ρ * (ρ / dist p z) = t := by
    field_simp [(dist_pos.mpr hne.symm).ne', hρ.ne']
  rw [smul_smul, hcoef]

@[grind =]
lemma segment_inter_closedBall_eq_radial (p z : V) {ρ : ℝ} (hρ : 0 < ρ) (hne : z ≠ p)
    (hlt : ρ ≤ dist p z) :
    closedBall p ρ ∩ segment ℝ p z = segment ℝ p (radialPoint p z ρ) := by
  apply subset_antisymm
  · intro w ⟨hwball, hwseg⟩
    obtain ⟨t, ⟨ht0, _ht1⟩, rfl⟩ :=
      (segment_eq_image_lineMap (𝕜 := ℝ) p z).symm ▸ hwseg
    have htdist : t * dist p z ≤ ρ := by
      have : dist (AffineMap.lineMap p z t) p ≤ ρ := mem_closedBall.mp hwball
      rwa [dist_lineMap_left_of_nonneg p z ht0] at this
    rw [lineMap_eq_lineMap_radial p z hρ hne, segment_eq_image_lineMap]
    refine ⟨t * dist p z / ρ, ⟨div_nonneg (mul_nonneg ht0 dist_nonneg) hρ.le, ?_⟩, rfl⟩
    exact div_le_one_of_le₀ htdist hρ.le
  intro w hw
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ :=
    (segment_eq_image_lineMap (𝕜 := ℝ) p (radialPoint p z ρ)).symm ▸ hw
  refine ⟨?_, ?_⟩
  · rw [mem_closedBall, dist_lineMap_left_of_nonneg _ _ ht0,
      dist_comm p (radialPoint p z ρ), dist_radialPoint p z hρ.le hne]
    exact mul_le_of_le_one_left hρ.le ht1
  exact segment_subset_segment_right (radialPoint_mem_segment p z hρ.le hlt) hw

/-- Not `@[simp]`: `mem_sphere_iff_norm` (`@[simp high]`) plus `norm_radialPoint_sub` already close
this goal, so a second rule for the same content would be activated without ever contributing. It
is kept as a named lemma because it is the ergonomic form — every call site wants it. -/
@[grind .]
lemma mem_sphere_radialPoint (p z : V) {ρ : ℝ} (hρ : 0 ≤ ρ) (hne : z ≠ p) :
    radialPoint p z ρ ∈ sphere p ρ := by
  simp [hρ, hne]

@[grind .]
lemma radialPoint_ne_of_mem_openSegment (p a b : V) {ρ : ℝ} (hρ : 0 < ρ) (hab : a ≠ b)
    (hp : p ∈ openSegment ℝ a b) :
    radialPoint p a ρ ≠ radialPoint p b ρ := by
  intro heq
  obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ :=
    (openSegment_eq_image_lineMap (𝕜 := ℝ) a b).symm ▸ hp
  set q := AffineMap.lineMap a b t
  have hp' : q ∈ openSegment ℝ a b := hp
  have hab_pos : 0 < dist a b := dist_pos.mpr hab
  have haq : a - q = t • (a - b) := by
    dsimp [q]; simp [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub]; module
  have hbq : b - q = (1 - t) • (b - a) := by
    dsimp [q]; simp [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub]; module
  have hq_a : dist q a = t * dist a b := by
    rw [dist_eq_norm, show q - a = t • (b - a) by
      dsimp [q]; simp [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub],
      norm_smul, Real.norm_eq_abs, abs_of_nonneg ht0.le, ← dist_eq_norm,
      PseudoMetricSpace.dist_comm]
  have hq_b : dist q b = (1 - t) * dist a b := by
    have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht1.le
    rw [dist_eq_norm, show q - b = (t - 1) • (b - a) by
      dsimp [q]; simp [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub]; module,
      norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr ht1.le), neg_sub,
      ← dist_eq_norm, PseudoMetricSpace.dist_comm]
  change radialPoint q a ρ = radialPoint q b ρ at heq
  unfold radialPoint at heq
  simp only [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub] at heq
  have hmul : (ρ / dist q a) • (a - q) = (ρ / dist q b) • (b - q) :=
    add_right_cancel heq
  have hrew : (1 - t) • (b - a) = -((1 - t) • (a - b)) := by rw [← smul_neg, neg_sub]
  rw [haq, hbq, hrew, smul_neg, smul_smul, smul_smul] at hmul
  have hposL : 0 < ρ / dist q a * t :=
    mul_pos (div_pos hρ (by rw [hq_a]; exact mul_pos ht0 hab_pos)) ht0
  have hposR : 0 < ρ / dist q b * (1 - t) :=
    mul_pos (div_pos hρ (by rw [hq_b]; exact mul_pos (sub_pos.mpr ht1) hab_pos))
      (sub_pos.mpr ht1)
  have hv : (ρ / dist q a * t + ρ / dist q b * (1 - t)) • (a - b) = 0 := by
    rw [add_smul, hmul, neg_add_cancel]
  exact (sub_ne_zero.mpr hab) ((smul_eq_zero.mp hv).resolve_left (add_pos hposL hposR).ne')

@[grind =]
lemma closedBall_inter_segment_eq_two_radii (p a b : V) {ρ : ℝ} (hρ : 0 < ρ) (hab : a ≠ b)
    (hp : p ∈ openSegment ℝ a b) (ha : ρ ≤ dist p a) (hb : ρ ≤ dist p b) :
    closedBall p ρ ∩ segment ℝ a b =
      segment ℝ p (radialPoint p a ρ) ∪ segment ℝ p (radialPoint p b ρ) := by
  have hne_a := ne_of_mem_openSegment_left hab hp
  have hne_b := ne_of_mem_openSegment_right hab hp
  have hqseg : p ∈ segment ℝ a b := openSegment_subset_segment ℝ a b hp
  apply subset_antisymm
  · intro x ⟨hxball, hxseg⟩
    have hx' : x ∈ segment ℝ a p ∪ segment ℝ p b := by
      rwa [← segment_union_eq_segment hqseg] at hxseg
    rcases hx' with hx1 | hx2
    · have : x ∈ closedBall p ρ ∩ segment ℝ p a := ⟨hxball, by rwa [segment_symm]⟩
      exact Or.inl <| (segment_inter_closedBall_eq_radial p a hρ hne_a ha) ▸ this
    · exact Or.inr <|
        (segment_inter_closedBall_eq_radial p b hρ hne_b hb) ▸ ⟨hxball, hx2⟩
  refine fun x hx ↦ ⟨?_, ?_⟩
  · obtain hx | hx := hx
    · exact (convex_closedBall p ρ).segment_subset (mem_closedBall_self hρ.le)
        (sphere_subset_closedBall (mem_sphere_radialPoint p a hρ.le hne_a)) hx
    · exact (convex_closedBall p ρ).segment_subset (mem_closedBall_self hρ.le)
        (sphere_subset_closedBall (mem_sphere_radialPoint p b hρ.le hne_b)) hx
  obtain hx | hx := hx
  · have hrad := radialPoint_mem_segment p a hρ.le ha
    have hsub : segment ℝ p (radialPoint p a ρ) ⊆ segment ℝ a b :=
      (segment_subset_segment_right hrad).trans <| by
        rw [← segment_union_eq_segment hqseg, segment_symm]; exact subset_union_left
    exact hsub hx
  have hrad := radialPoint_mem_segment p b hρ.le hb
  have hsub : segment ℝ p (radialPoint p b ρ) ⊆ segment ℝ a b :=
    (segment_subset_segment_right hrad).trans <| by
      rw [← segment_union_eq_segment hqseg]; exact subset_union_right
  exact hsub hx


@[grind =]
lemma closedBall_inter_two_segments_at_endpoint (p a b : V) {ρ : ℝ} (hρ : 0 < ρ)
    (hne_a : a ≠ p) (hne_b : b ≠ p) (ha : ρ ≤ dist p a) (hb : ρ ≤ dist p b) :
    closedBall p ρ ∩ (segment ℝ a p ∪ segment ℝ p b) =
      segment ℝ p (radialPoint p a ρ) ∪ segment ℝ p (radialPoint p b ρ) := by
  apply subset_antisymm
  · intro x ⟨hxball, hx⟩
    obtain hx | hx := hx
    · have : x ∈ closedBall p ρ ∩ segment ℝ p a := ⟨hxball, by rwa [segment_symm]⟩
      exact Or.inl <| (segment_inter_closedBall_eq_radial p a hρ hne_a ha) ▸ this
    · exact Or.inr <| (segment_inter_closedBall_eq_radial p b hρ hne_b hb) ▸ ⟨hxball, hx⟩
  refine fun x hx ↦ ⟨?_, ?_⟩
  · obtain hx | hx := hx
    · exact (convex_closedBall p ρ).segment_subset (mem_closedBall_self hρ.le)
        (sphere_subset_closedBall (mem_sphere_radialPoint p a hρ.le hne_a)) hx
    · exact (convex_closedBall p ρ).segment_subset (mem_closedBall_self hρ.le)
        (sphere_subset_closedBall (mem_sphere_radialPoint p b hρ.le hne_b)) hx
  obtain hx | hx := hx
  · have hrad := radialPoint_mem_segment p a hρ.le ha
    exact Or.inl <| by
      rw [segment_symm]
      exact segment_subset_segment_right hrad hx
  exact Or.inr <| segment_subset_segment_right (radialPoint_mem_segment p b hρ.le hb) hx

@[grind =]
lemma radialPoint_eq_iff_pos_parallel (p a b : V) {ρ : ℝ} (hρ : 0 < ρ)
    (hne_a : a ≠ p) (hne_b : b ≠ p) :
    radialPoint p a ρ = radialPoint p b ρ ↔
      ∃ t : ℝ, 0 < t ∧ a - p = t • (b - p) := by
  refine ⟨?_, ?_⟩
  · intro heq
    unfold radialPoint at heq
    simp only [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub] at heq
    have hmul : (ρ / dist p a) • (a - p) = (ρ / dist p b) • (b - p) :=
      add_right_cancel heq
    have hda : 0 < dist p a := dist_pos.mpr hne_a.symm
    have hdb : 0 < dist p b := dist_pos.mpr hne_b.symm
    refine ⟨dist p a / dist p b, div_pos hda hdb, ?_⟩
    have := congr_arg (fun z : V ↦ (dist p a / ρ) • z) hmul
    simp only [smul_smul] at this
    have h1 : dist p a / ρ * (ρ / dist p a) = 1 := by field_simp [hρ.ne', hda.ne']
    have h2 : dist p a / ρ * (ρ / dist p b) = dist p a / dist p b := by
      field_simp [hρ.ne', hdb.ne']
    rwa [h1, one_smul, h2] at this
  rintro ⟨t, ht, hab⟩
  unfold radialPoint
  simp only [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub]
  have hda : 0 < dist p a := dist_pos.mpr hne_a.symm
  have hdb : 0 < dist p b := dist_pos.mpr hne_b.symm
  have hdist : dist p a = t * dist p b := by
    have : ‖a - p‖ = t * ‖b - p‖ := by
      rw [hab, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
    simp only [dist_eq_norm]
    rw [norm_sub_rev, this, norm_sub_rev]
  have : (ρ / dist p a) • (a - p) = (ρ / dist p b) • (b - p) := by
    rw [hab, smul_smul, hdist, mul_comm t]
    field_simp [hda.ne', hdb.ne', ht.ne']
  exact congrArg (· + p) this

/-- **A radius meets its sphere only at the far end.** If `w` is at distance `ρ` from `p`, the only
point of `segment ℝ p w` at distance `ρ` from `p` is `w` itself.

The uniqueness counterpart to `mem_sphere_radialPoint`, which supplies existence. Together they say
that `segment ℝ p w ∩ sphere p ρ` is a single point, which is what lets a caller reading a radius
off a star equation conclude that the radius it found is *the* one it was looking for. -/
@[grind →]
lemma eq_of_mem_segment_of_mem_sphere (p : V) {ρ : ℝ} (hρ : 0 < ρ) {w y : V}
    (hw : w ∈ sphere p ρ) (hy : y ∈ segment ℝ p w) (hysph : y ∈ sphere p ρ) : y = w := by
  rw [segment_eq_image_lineMap] at hy
  obtain ⟨t, ⟨ht0, _⟩, rfl⟩ := hy
  have hd : dist (AffineMap.lineMap p w t) p = t * dist p w := dist_lineMap_left_of_nonneg p w ht0
  rw [mem_sphere] at hysph hw
  rw [hysph, dist_comm p w, hw] at hd
  rw [(mul_eq_right₀ hρ.ne').mp hd.symm, AffineMap.lineMap_apply_one]

/-- **Same direction implies overlap.** If two points give the same radius at `p`, the segments to
them share a nondegenerate initial segment at `p`.

This is the primitive that converts a disjointness hypothesis into distinctness of directions: if
two pieces of a set meet only at `p` and each contains a segment out of `p`, those segments cannot
be positively parallel, since by this lemma they would then share more than `p`. It is the
consumer-facing half of `radialPoint_eq_iff_pos_parallel`, which says *when* two radii coincide.

Neither `z₁ ≠ p` nor `z₂ ≠ p` is a hypothesis: both follow from `hρ` and the corresponding `hle`,
since `0 < ρ ≤ dist p zᵢ`.

Route: `radialPoint_mem_segment` puts `radialPoint p z₁ ρ ∈ segment ℝ p z₁`, and `heq` puts the same
point in `segment ℝ p z₂`. `segment_subset_segment_right` (`Convex/Segment.lean`) upgrades each of
those to the whole initial segment. `≠ p` is `mem_sphere_radialPoint` with `hρ.ne'`. -/
@[grind →]
lemma exists_segment_subset_inter_of_radialPoint_eq (p : V) {z₁ z₂ : V} {ρ : ℝ} (hρ : 0 < ρ)
    (hle₁ : ρ ≤ dist p z₁) (hle₂ : ρ ≤ dist p z₂)
    (heq : radialPoint p z₁ ρ = radialPoint p z₂ ρ) :
    ∃ w ≠ p, segment ℝ p w ⊆ segment ℝ p z₁ ∩ segment ℝ p z₂ :=
  ⟨radialPoint p z₁ ρ,
    ne_of_mem_sphere
      (mem_sphere_radialPoint p z₁ hρ.le (dist_pos.mp (hρ.trans_le hle₁)).symm) hρ.ne',
    subset_inter (segment_subset_segment_right (radialPoint_mem_segment p z₁ hρ.le hle₁))
      (heq ▸ segment_subset_segment_right (radialPoint_mem_segment p z₂ hρ.le hle₂))⟩

/-- **The closed radius minus the open ball is the sphere endpoint.** For `z` on `sphere p ρ`,
`segment ℝ p z` leaves `ball p ρ` only at `z`.

The complement to `segment_inter_closedBall_eq_radial`, which describes the part of a segment
*inside* a ball: together they say a radius meets the ball in a radius and the exterior in a point.
Consumers use it to identify the endpoint of a cell that has been cut at a ball. -/
@[grind =]
lemma segment_diff_ball_eq_singleton {p z : V} {ρ : ℝ} (hρ : 0 < ρ) (hz : dist z p = ρ) :
    segment ℝ p z \ ball p ρ = {z} := by
  refine subset_antisymm ?_ ?_
  · intro w hw
    have hwseg : w ∈ segment ℝ p z := hw.1
    have hwr : ρ ≤ dist w p := by simpa [mem_ball, not_lt] using hw.2
    exact eq_of_mem_segment_of_mem_sphere p hρ (mem_sphere.mpr hz) hwseg <| mem_sphere.mpr <|
      le_antisymm
        (mem_closedBall.mp <| (convex_closedBall p ρ).segment_subset
          (mem_closedBall_self hρ.le) (mem_closedBall.mpr hz.le) hwseg) hwr
  intro w hw
  rw [mem_singleton_iff] at hw
  subst w
  refine ⟨right_mem_segment ℝ p z, ?_⟩
  simpa [mem_ball, not_lt, dist_comm z p] using hz.symm.le

/-- **Two radii of one ball meet only at the centre**, when they end at distinct points of its
sphere. True in any normed space: a point of `[p, z]` with `‖z - p‖ = ρ` is pinned down by its
distance to `p`.

The consumer-facing converse of `radialPoint_eq_iff_pos_parallel`. That lemma says *when* two radii
coincide — same direction; this one says what follows when their endpoints differ, which is the
form every caller wants, because a caller has distinct endpoints (from a disjointness hypothesis)
and wants the intersection.

The common radius is spelled `dist z₂ p = dist z₁ p` rather than introducing a named `ρ` with
`dist zᵢ p = ρ`, and that is a *tagging* constraint, not a stylistic one. `@[grind =]` keys on the
left-hand side, so every variable of the lemma has to be determined by it; a phantom `ρ` occurring
only in the hypotheses makes the pattern uninstantiable and the attribute is rejected outright with
`invalid pattern(s)`. Eliminating `ρ` also drops a hypothesis: `0 < ρ` becomes `z₁ ≠ p`. -/
@[grind =]
lemma segment_radial_inter_eq_center {p z₁ z₂ : V} (hne₁ : z₁ ≠ p)
    (heq : dist z₂ p = dist z₁ p) (hne : z₁ ≠ z₂) :
    segment ℝ p z₁ ∩ segment ℝ p z₂ = {p} := by
  set ρ := dist z₁ p with hρdef
  have hρ : 0 < ρ := dist_pos.mpr hne₁
  have hz₁ : dist z₁ p = ρ := rfl
  have hz₂ : dist z₂ p = ρ := heq
  clear_value ρ
  refine subset_antisymm ?_ (by simp [left_mem_segment])
  intro w ⟨hw₁, hw₂⟩
  by_cases hwr : dist w p = ρ
  · have hwz₁ := eq_of_mem_segment_of_mem_sphere p hρ (mem_sphere.mpr hz₁) hw₁ (mem_sphere.mpr hwr)
    have hwz₂ := eq_of_mem_segment_of_mem_sphere p hρ (mem_sphere.mpr hz₂) hw₂ (mem_sphere.mpr hwr)
    exact (hne (hwz₁.symm.trans hwz₂)).elim
  obtain ⟨t, ⟨ht0, _⟩, rfl⟩ := (segment_eq_image_lineMap (𝕜 := ℝ) p z₁).symm ▸ hw₁
  obtain ⟨s, ⟨hs0, _⟩, hws⟩ := (segment_eq_image_lineMap (𝕜 := ℝ) p z₂).symm ▸ hw₂
  have hts : t • (z₁ - p) = s • (z₂ - p) := by
    have := congrArg (fun z : V ↦ z - p) hws.symm
    simpa [AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub, add_sub_cancel_right] using this
  by_cases ht : t = 0
  · simp [ht, AffineMap.lineMap_apply]
  · have hmul : z₁ - p = (s / t) • (z₂ - p) := by
      calc
        z₁ - p = (t⁻¹ * t) • (z₁ - p) := by rw [inv_mul_cancel₀ ht, one_smul]
        _ = t⁻¹ • (t • (z₁ - p)) := by rw [mul_smul]
        _ = t⁻¹ • (s • (z₂ - p)) := by rw [hts]
        _ = (t⁻¹ * s) • (z₂ - p) := by rw [smul_smul]
        _ = (s / t) • (z₂ - p) := by rw [div_eq_mul_inv, mul_comm]
    have habs : |s / t| = 1 := by
      have hz₁' : ‖z₁ - p‖ = ρ := by simpa [dist_eq_norm] using hz₁
      have hz₂' : ‖z₂ - p‖ = ρ := by simpa [dist_eq_norm] using hz₂
      have : ‖z₁ - p‖ = |s / t| * ‖z₂ - p‖ := by
        rw [hmul, norm_smul, Real.norm_eq_abs]
      rwa [hz₁', hz₂', eq_comm, mul_eq_right₀ hρ.ne'] at this
    have hst : s / t = 1 := by
      have hnonneg : 0 ≤ s / t := div_nonneg hs0 ht0
      rwa [abs_of_nonneg hnonneg] at habs
    have : z₁ = z₂ := sub_left_inj.mp (by rwa [hst, one_smul] at hmul)
    exact (hne this).elim

/-- **A point on two radii of one ball is the centre.** The pointwise form of
`segment_radial_inter_eq_center`.

This exists because of how `grind` matches, and the reason generalises. `@[grind =]` fires only
where its left-hand side occurs *as a term*: a caller holding `w ∈ segment ℝ p z₁` and
`w ∈ segment ℝ p z₂` has the two memberships but never forms `segment ℝ p z₁ ∩ segment ℝ p z₂`,
so the set-level rule has nothing to rewrite and stays silent. Keying the same content on the
antecedents with `@[grind →]` reaches that caller. Tagging both is not redundant — they fire in
disjoint situations, and the set form is still the one to use when an intersection is in hand. -/
@[grind →]
lemma eq_center_of_mem_two_radii {p z₁ z₂ w : V} (hne₁ : z₁ ≠ p)
    (heq : dist z₂ p = dist z₁ p) (hne : z₁ ≠ z₂)
    (h₁ : w ∈ segment ℝ p z₁) (h₂ : w ∈ segment ℝ p z₂) : w = p := by
  have hmem : w ∈ ({p} : Set V) := by
    rw [← segment_radial_inter_eq_center hne₁ heq hne]; exact ⟨h₁, h₂⟩
  exact mem_singleton_iff.mp hmem

@[grind =]
lemma two_radii_union_eq_star (p ya yb : V) :
    (segment ℝ p ya ∪ segment ℝ p yb : Set V) =
      ({p} : Set V) ∪ (segment ℝ p ya ∪ segment ℝ p yb) := by
  ext x
  simp only [mem_union, mem_singleton_iff]
  refine ⟨?_, ?_⟩
  · exact Or.inr
  rintro (rfl | h)
  · exact Or.inl (left_mem_segment _ _ _)
  exact h

/-- **A point of a radius at distance exactly `ρ` is the radial point.** The pointwise form of
`segment_inter_closedBall_eq_radial`.

Second instance of the pattern that produced `eq_center_of_mem_two_radii`, and the reason it is
worth stating as a rule: the set-level `@[grind =]` rewrite fires only where
`closedBall p ρ ∩ segment ℝ p z` occurs *as a term*, and a caller holding `y ∈ segment ℝ p z` and
`y ∈ sphere p ρ` never forms it. Without this lemma the goal below is out of `grind`'s reach —
verified, it was a standing unproved probe in `WIP/GrindProbe.lean`, a file that could never build
because `WIP` is not a `lean_lib`. **Whenever a set-level equation gets `@[grind =]`, ask what its
pointwise consequence is and tag that too.** -/
@[grind →]
lemma eq_radialPoint_of_mem_segment_of_mem_sphere (p z : V) {ρ : ℝ} (hρ : 0 < ρ) (hne : z ≠ p)
    (hle : ρ ≤ dist p z) {y : V} (hyseg : y ∈ segment ℝ p z) (hysph : y ∈ sphere p ρ) :
    y = radialPoint p z ρ := by
  have hy : y ∈ closedBall p ρ ∩ segment ℝ p z := ⟨sphere_subset_closedBall hysph, hyseg⟩
  rw [segment_inter_closedBall_eq_radial p z hρ hne hle] at hy
  exact eq_of_mem_segment_of_mem_sphere p hρ (mem_sphere_radialPoint p z hρ.le hne) hy hysph

/-! ### Regression tests for the tags

Each `example` below fails if the corresponding tag is removed. This is the only way to find out
that a tag fires: a tag that never matches produces no error, no warning and no failing proof, it
just costs a match attempt forever. These are also the `grind` call sites that
`grind.unusedLemmaThreshold` needs in order to measure anything over this API at all — without them
the file is unmeasurable, and "no `grind` call mentions `radialPoint`" is a statement about the
absence of tests, not evidence that tagging is premature. -/

section RegressionTests

variable {p z z₁ z₂ w y : V} {ρ : ℝ}

-- `norm_radialPoint_sub`, in the ambient normed normal form.
example (hρ : 0 ≤ ρ) (hne : z ≠ p) : ‖radialPoint p z ρ - p‖ = ρ := by grind

-- `mem_sphere_radialPoint` and `radialPoint_mem_segment`, whose hypotheses are side conditions.
example (hρ : 0 ≤ ρ) (hne : z ≠ p) (hle : ρ ≤ dist p z) :
    radialPoint p z ρ ∈ sphere p ρ ∧ radialPoint p z ρ ∈ segment ℝ p z := by grind

-- `segment_inter_closedBall_eq_radial`: truncating a radius to a ball.
example (hρ : 0 < ρ) (hne : z ≠ p) (hle : ρ ≤ dist p z) :
    closedBall p ρ ∩ segment ℝ p z = segment ℝ p (radialPoint p z ρ) := by grind

-- `eq_of_mem_segment_of_mem_sphere`: a radius meets its sphere once. Keyed on the antecedents,
-- so this closes only because the `∈ segment` / `∈ sphere` hypotheses are present to match.
example (hρ : 0 < ρ) (hw : w ∈ sphere p ρ) (hy : y ∈ segment ℝ p w) (hysph : y ∈ sphere p ρ) :
    y = w := by grind

-- `segment_diff_ball_eq_singleton`: the part of a radius outside the open ball.
example (hρ : 0 < ρ) (hz : dist z p = ρ) : segment ℝ p z \ ball p ρ = {z} := by grind

-- `segment_radial_inter_eq_center`: two radii of one ball with distinct sphere endpoints.
example (hne₁ : z₁ ≠ p) (heq : dist z₂ p = dist z₁ p) (hne : z₁ ≠ z₂) :
    segment ℝ p z₁ ∩ segment ℝ p z₂ = {p} := by grind

-- The consumer-facing use of the previous one: a point on both radii is the centre. This is the
-- form that actually appears downstream, and it closes only because the tag is `=` rather than
-- `→`: `grind` rewrites the intersection it already has, instead of having to guess the lemma.
example (hne₁ : z₁ ≠ p) (heq : dist z₂ p = dist z₁ p) (hne : z₁ ≠ z₂)
    (h₁ : w ∈ segment ℝ p z₁) (h₂ : w ∈ segment ℝ p z₂) : w = p := by grind

-- The `ρ`-shaped call, which is how callers carrying a named radius reach the lemma. The `dist_pos`
-- hint is needed and is not an oversight: the side condition `z₁ ≠ p` follows from `0 < ρ` and
-- `dist z₁ p = ρ` only through `dist_pos`, which is untagged in Mathlib. A caller in this shape
-- pays one hint; that is the price of the phantom `ρ` living in the caller rather than the lemma.
example (hρ : 0 < ρ) (hz₁ : dist z₁ p = ρ) (hz₂ : dist z₂ p = ρ) (hne : z₁ ≠ z₂) :
    segment ℝ p z₁ ∩ segment ℝ p z₂ = {p} := by grind [dist_pos]

-- From `WIP/GrindProbe.lean`, which could not build (`WIP` is not a `lean_lib`) and is now deleted:
-- a point of a radius at distance exactly `ρ` *is* the radial point. Composes
-- `segment_inter_closedBall_eq_radial` with `eq_of_mem_segment_of_mem_sphere`.
example (hρ : 0 < ρ) (hzne : z ≠ p) (hle : ρ ≤ dist p z)
    (hyseg : y ∈ segment ℝ p z) (hysph : y ∈ sphere p ρ) : y = radialPoint p z ρ := by grind

end RegressionTests
