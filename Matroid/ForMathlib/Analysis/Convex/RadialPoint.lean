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

### No `grind` tags, yet

None of these carry `@[grind]`. A `grind` E-matching rule earns its keep only when there are
`grind` calls whose goals mention `radialPoint`, and there are currently none anywhere in the
project. Tagging now would add a rule that is activated whenever `radialPoint` appears and never
contributes to a proof term — exactly what `scripts/grind_unused_lemmas.sh` and
`set_option grind.unusedLemmaThreshold` exist to flag. Revisit when the first `grind` proof over
this API appears; `dist_radialPoint` is then the natural `@[grind =]` candidate, for the same
bounded-cost reason that made it a candidate for `@[simp]`.
-/

@[expose] public section

open Set Metric

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

lemma dist_lineMap_left_of_nonneg (p z : V) {t : ℝ} (ht : 0 ≤ t) :
    dist (AffineMap.lineMap p z t) p = t * dist p z := by
  rw [dist_lineMap_left, Real.norm_eq_abs, abs_of_nonneg ht]

noncomputable def radialPoint (p z : V) (ρ : ℝ) : V :=
  AffineMap.lineMap p z (ρ / dist p z)

/-- The defining property, at the `dist` level. Oriented with the constructed point on the left,
matching `mem_sphere`, `mem_closedBall` and Mathlib's `dist_lineMap_left`.

Deliberately **not** `@[simp]`: see `norm_radialPoint_sub` for the tagged form. -/
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
@[simp]
lemma norm_radialPoint_sub (p z : V) {ρ : ℝ} (hρ : 0 ≤ ρ) (hne : z ≠ p) :
    ‖radialPoint p z ρ - p‖ = ρ := by
  rw [← dist_eq_norm]
  exact dist_radialPoint p z hρ hne

lemma radialPoint_mem_segment (p z : V) {ρ : ℝ} (hρ : 0 ≤ ρ) (hle : ρ ≤ dist p z) :
    radialPoint p z ρ ∈ segment ℝ p z := by
  rw [radialPoint, segment_eq_image_lineMap]
  refine ⟨ρ / dist p z, ⟨div_nonneg hρ dist_nonneg, ?_⟩, rfl⟩
  exact div_le_one_of_le₀ hle dist_nonneg

private lemma lineMap_eq_lineMap_radial (p z : V) {ρ t : ℝ} (hρ : 0 < ρ) (hne : z ≠ p) :
    AffineMap.lineMap p z t =
      AffineMap.lineMap p (radialPoint p z ρ) (t * dist p z / ρ) := by
  have hzpos : 0 < dist p z := dist_pos.mpr hne.symm
  simp only [radialPoint, AffineMap.lineMap_apply, vadd_eq_add, vsub_eq_sub, add_sub_cancel_right]
  have hcoef : t * dist p z / ρ * (ρ / dist p z) = t := by
    field_simp [hzpos.ne', hρ.ne']
  rw [smul_smul, hcoef]

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
  · intro w hw
    obtain ⟨t, ⟨ht0, ht1⟩, rfl⟩ :=
      (segment_eq_image_lineMap (𝕜 := ℝ) p (radialPoint p z ρ)).symm ▸ hw
    refine ⟨?_, ?_⟩
    · rw [mem_closedBall, dist_lineMap_left_of_nonneg _ _ ht0,
        dist_comm p (radialPoint p z ρ), dist_radialPoint p z hρ.le hne]
      exact mul_le_of_le_one_left hρ.le ht1
    · exact (convex_segment p z).segment_subset (left_mem_segment ℝ p z)
        (radialPoint_mem_segment p z hρ.le hlt) hw

/-- Not `@[simp]`: `mem_sphere_iff_norm` (`@[simp high]`) plus `norm_radialPoint_sub` already close
this goal, so a second rule for the same content would be activated without ever contributing. It
is kept as a named lemma because it is the ergonomic form — every call site wants it. -/
lemma mem_sphere_radialPoint (p z : V) {ρ : ℝ} (hρ : 0 ≤ ρ) (hne : z ≠ p) :
    radialPoint p z ρ ∈ sphere p ρ := by
  simp [hρ, hne]

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
  have hab_ne : a - b ≠ 0 := sub_ne_zero.mpr hab
  have hposL : 0 < ρ / dist q a * t :=
    mul_pos (div_pos hρ (by rw [hq_a]; exact mul_pos ht0 hab_pos)) ht0
  have hposR : 0 < ρ / dist q b * (1 - t) :=
    mul_pos (div_pos hρ (by rw [hq_b]; exact mul_pos (sub_pos.mpr ht1) hab_pos))
      (sub_pos.mpr ht1)
  have hv : (ρ / dist q a * t + ρ / dist q b * (1 - t)) • (a - b) = 0 := by
    rw [add_smul, hmul, neg_add_cancel]
  exact hab_ne ((smul_eq_zero.mp hv).resolve_left (add_pos hposL hposR).ne')

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
  · intro x hx
    refine ⟨?_, ?_⟩
    · rcases hx with hx | hx
      · exact (convex_closedBall p ρ).segment_subset (mem_closedBall_self hρ.le)
          (sphere_subset_closedBall (mem_sphere_radialPoint p a hρ.le hne_a)) hx
      · exact (convex_closedBall p ρ).segment_subset (mem_closedBall_self hρ.le)
          (sphere_subset_closedBall (mem_sphere_radialPoint p b hρ.le hne_b)) hx
    · rcases hx with hx | hx
      · have hrad := radialPoint_mem_segment p a hρ.le ha
        have hsub : segment ℝ p (radialPoint p a ρ) ⊆ segment ℝ a b :=
          ((convex_segment p a).segment_subset (left_mem_segment _ _ _) hrad).trans <| by
            rw [← segment_union_eq_segment hqseg, segment_symm]; exact subset_union_left
        exact hsub hx
      · have hrad := radialPoint_mem_segment p b hρ.le hb
        have hsub : segment ℝ p (radialPoint p b ρ) ⊆ segment ℝ a b :=
          ((convex_segment p b).segment_subset (left_mem_segment _ _ _) hrad).trans <| by
            rw [← segment_union_eq_segment hqseg]; exact subset_union_right
        exact hsub hx


lemma closedBall_inter_two_segments_at_endpoint (p a b : V) {ρ : ℝ} (hρ : 0 < ρ)
    (hne_a : a ≠ p) (hne_b : b ≠ p) (ha : ρ ≤ dist p a) (hb : ρ ≤ dist p b) :
    closedBall p ρ ∩ (segment ℝ a p ∪ segment ℝ p b) =
      segment ℝ p (radialPoint p a ρ) ∪ segment ℝ p (radialPoint p b ρ) := by
  apply subset_antisymm
  · intro x ⟨hxball, hx⟩
    rcases hx with hx | hx
    · have : x ∈ closedBall p ρ ∩ segment ℝ p a := ⟨hxball, by rwa [segment_symm]⟩
      exact Or.inl <| (segment_inter_closedBall_eq_radial p a hρ hne_a ha) ▸ this
    · exact Or.inr <| (segment_inter_closedBall_eq_radial p b hρ hne_b hb) ▸ ⟨hxball, hx⟩
  · intro x hx
    refine ⟨?_, ?_⟩
    · rcases hx with hx | hx
      · exact (convex_closedBall p ρ).segment_subset (mem_closedBall_self hρ.le)
          (sphere_subset_closedBall (mem_sphere_radialPoint p a hρ.le hne_a)) hx
      · exact (convex_closedBall p ρ).segment_subset (mem_closedBall_self hρ.le)
          (sphere_subset_closedBall (mem_sphere_radialPoint p b hρ.le hne_b)) hx
    · rcases hx with hx | hx
      · have hrad := radialPoint_mem_segment p a hρ.le ha
        exact Or.inl <| by
          rw [segment_symm]
          exact (convex_segment p a).segment_subset (left_mem_segment _ _ _) hrad hx
      · exact Or.inr <|
          (convex_segment p b).segment_subset (left_mem_segment _ _ _)
            (radialPoint_mem_segment p b hρ.le hb) hx

lemma radialPoint_eq_iff_pos_parallel (p a b : V) {ρ : ℝ} (hρ : 0 < ρ)
    (hne_a : a ≠ p) (hne_b : b ≠ p) :
    radialPoint p a ρ = radialPoint p b ρ ↔
      ∃ t : ℝ, 0 < t ∧ a - p = t • (b - p) := by
  constructor
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
  · rintro ⟨t, ht, hab⟩
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

lemma two_radii_union_eq_star (p ya yb : V) :
    (segment ℝ p ya ∪ segment ℝ p yb : Set V) =
      ({p} : Set V) ∪ (segment ℝ p ya ∪ segment ℝ p yb) := by
  ext x
  simp only [mem_union, mem_singleton_iff]
  constructor
  · exact Or.inr
  · rintro (rfl | h)
    · exact Or.inl (left_mem_segment _ _ _)
    · exact h
