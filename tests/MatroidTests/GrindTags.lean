module

public import Matroid.ForMathlib.Analysis.Convex.RadialPoint
public import Matroid.ForMathlib.Topology.MetricSpace
public import Matroid.ForMathlib.Topology.Path

/-!
# Regression tests: `grind` and `simp` tags

Each `example` here fails if the tag or hint named above it is removed. They exist for three
reasons, and the third is the one that is easy to miss:

1. It is the only way to learn that a tag *fires*. A tag that never matches produces no error, no
   warning and no failing proof; it just costs a match attempt forever.
2. It catches silent over-general keying, which the loud `grind` error messages do not.
3. It is the measurement harness. `grind.unusedLemmaThreshold` can only report on `grind` calls
   that exist, so a tagged API with no tests is *unmeasurable* — and "untested" and "unmeasurable"
   are then the same condition.

Write the test for the shape a **caller** will actually have, not the lemma restated. Restating the
lemma tests almost nothing; the informative test is the one a step below it, and when that one
fails it usually means the API is missing the consumer-facing form rather than that the tag is
wrong. See `notes/lean/Assimilation.md`, stage 3, and `tests/README.md`.
-/

section RadialPoint

open Set Metric

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {p z z₁ z₂ w y : V} {ρ : ℝ}

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

-- A point of a radius at distance exactly `ρ` *is* the radial point. Composes
-- `segment_inter_closedBall_eq_radial` with `eq_of_mem_segment_of_mem_sphere`.
example (hρ : 0 < ρ) (hzne : z ≠ p) (hle : ρ ≤ dist p z)
    (hyseg : y ∈ segment ℝ p z) (hysph : y ∈ sphere p ρ) : y = radialPoint p z ρ := by grind

end RadialPoint

section MetricSpace

variable {X : Type*} [PseudoMetricSpace X]

-- `exists_pos_le_dist_of_notMem`, `@[grind →]`.
example {K : Set X} (hK : IsClosed K) {p : X} (hp : p ∉ K) : ∃ δ > 0, ∀ x ∈ K, δ ≤ dist p x := by
  grind

-- `exists_pos_le_dist_of_disjoint`, `@[grind →]`.
example {s t : Set X} (hs : IsCompact s) (ht : IsClosed t) (hst : Disjoint s t) :
    ∃ δ > 0, ∀ x ∈ s, ∀ y ∈ t, δ ≤ dist x y := by grind

end MetricSpace

section Path

open Set Metric unitInterval

-- `unitInterval.eq_zero_or_eq_one_or_mem_Ioo` as a hint: untaggable, so the caller names it.
example {t : I} (h₀ : t ≠ 0) (h₁ : t ≠ 1) : t ∈ Ioo (0 : I) 1 := by
  grind [unitInterval.eq_zero_or_eq_one_or_mem_Ioo]

-- Without the hint the same goal is out of reach, which is what makes the hint load-bearing.
example {t : I} (h₀ : t ≠ 0) (h₁ : t ≠ 1) : t = 0 ∨ t = 1 ∨ t ∈ Ioo (0 : I) 1 := by
  grind [unitInterval.eq_zero_or_eq_one_or_mem_Ioo]

-- `Path.image_Icc_subset_of_isConnected`, `@[grind →]`: keyed on the antecedents, which do mention
-- every variable, unlike `exists_lastExit_firstEntry` below.
example {α : Type*} [TopologicalSpace α] [T2Space α] {x y : α} {γ : Path x y}
    (hinj : Function.Injective γ) {S : Set α} (hS : IsConnected S) (hSsub : S ⊆ range γ)
    {t₁ t₂ : I} (h₁ : γ t₁ ∈ S) (h₂ : γ t₂ ∈ S) : γ '' Icc t₁ t₂ ⊆ S := by grind

-- `Path.exists_lastExit_firstEntry` is a *producer*, and `grind` cannot use it even as a hint:
-- `grind [Path.exists_lastExit_firstEntry]` is rejected with `failed to find an usable pattern
-- using different modifiers`, for the same reason both attribute forms were. The working shape is
-- to instantiate it and let `grind` consume the facts it yields. That is not a defect, and it is
-- the answer whenever a lemma's principal argument lives only under an existential.
example {α : Type*} [PseudoMetricSpace α] {a b c d : α} (γ : Path a b) {rc rd : ℝ}
    (hdisj : Disjoint (closedBall c rc) (closedBall d rd))
    (ha : a ∈ closedBall c rc) (hb : b ∈ closedBall d rd) :
    ∃ t : I, dist (γ t) c = rc ∧ γ t ∈ closedBall c rc := by
  obtain ⟨t, s, hts, hc, hd, hmc, hmd⟩ := γ.exists_lastExit_firstEntry hdisj ha hb
  grind [mem_closedBall]

end Path
