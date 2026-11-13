module

public import Matroid.MiniTauCeti.JCT.Topology.ConnectedComponent
public import Matroid.MiniTauCeti.JCT.Analysis.Normed.Module.ConnectedBall
public import Mathlib.Analysis.Normed.Module.Connected
public import Mathlib.Topology.Order.IntermediateValue

/-!
# Bounded regions and unbounded complementary components

Uniqueness of an unbounded complementary component selects a bounded side of a two-region
partition in a topological bornological space.

A bounded set in a nontrivial real normed space has an unbounded complementary component.
If the space has rank greater than one, every unbounded complementary component is the same.
The bounded set need not be closed.
-/

@[expose] public section

open Set Topology

namespace Bornology

/-- Uniqueness of an unbounded complementary component selects a bounded region from
a partition into two open connected regions with the same frontier. -/
theorem exists_bounded_compl_region {X : Type*} [TopologicalSpace X] [Bornology X]
    {C : Set X} (hunique : ∀ {p q : X},
      ¬ IsBounded (connectedComponentIn Cᶜ p) →
      ¬ IsBounded (connectedComponentIn Cᶜ q) →
      connectedComponentIn Cᶜ p = connectedComponentIn Cᶜ q)
    (hregions : ∃ U V : Set X, IsOpen U ∧ IsOpen V ∧ IsConnected U ∧ IsConnected V ∧
      Disjoint U V ∧ U ∪ V = Cᶜ ∧ frontier U = C ∧ frontier V = C) :
    ∃ U : Set X, U ⊆ Cᶜ ∧ IsBounded U ∧ IsConnected U ∧
      IsConnected (Cᶜ \ U) ∧ frontier U = C ∧ frontier (Cᶜ \ U) = C := by
  classical
  obtain ⟨U, V, hU, hV, hcU, hcV, hUV, hcover, hfU, hfV⟩ := hregions
  have hUC : U ⊆ Cᶜ := fun z hz ↦ hcover ▸ Or.inl hz
  have hVC : V ⊆ Cᶜ := fun z hz ↦ hcover ▸ Or.inr hz
  have hdiffU : Cᶜ \ U = V := by
    ext z
    constructor
    · intro hz
      exact (hcover.symm ▸ hz.1).resolve_left hz.2
    · intro hz
      exact ⟨hVC hz, fun hzU ↦ disjoint_left.mp hUV hzU hz⟩
  have hdiffV : Cᶜ \ V = U := by
    ext z
    constructor
    · intro hz
      exact (hcover.symm ▸ hz.1).resolve_right hz.2
    · intro hz
      exact ⟨hUC hz, fun hzV ↦ disjoint_left.mp hUV hz hzV⟩
  by_cases hbU : IsBounded U
  · exact ⟨U, hUC, hbU, hcU, hdiffU ▸ hcV, hfU, hdiffU ▸ hfV⟩
  have hbV : IsBounded V := by
    by_contra hbV
    obtain ⟨p, hp⟩ := hcU.nonempty
    obtain ⟨q, hq⟩ := hcV.nonempty
    have hUeq := eq_connectedComponentIn_of_frontier_subset hU hcU.isPreconnected
      (disjoint_left.mpr fun z hz hzC ↦ hUC hz hzC) hfU.le hp
    have hVeq := eq_connectedComponentIn_of_frontier_subset hV hcV.isPreconnected
      (disjoint_left.mpr fun z hz hzC ↦ hVC hz hzC) hfV.le hq
    have heq : U = V := hUeq.trans ((hunique (hUeq ▸ hbU) (hVeq ▸ hbV)).trans hVeq.symm)
    exact disjoint_left.mp hUV hp (heq ▸ hp)
  exact ⟨V, hVC, hbV, hcV, hdiffV ▸ hcU, hfV, hdiffV ▸ hfU⟩

/-- A ray outside a bounded set lies in an unbounded complementary component. -/
theorem exists_unbounded_connectedComponentIn_compl {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    {K : Set E} (hK : IsBounded K) :
    ∃ x : E, x ∉ K ∧ ¬ IsBounded (connectedComponentIn Kᶜ x) := by
  obtain ⟨v, hv⟩ : ∃ v : E, v ≠ 0 := exists_ne (0 : E)
  obtain ⟨R, hR⟩ := hK.exists_norm_le
  let t₀ : ℝ := max 1 ((R + 1) / ‖v‖)
  have hvpos : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have ht₀ : 0 ≤ t₀ := (by positivity : (0 : ℝ) ≤ (1 : ℝ)).trans (le_max_left ..)
  let ray : Set E := (fun t : ℝ ↦ t • v) '' Ici t₀
  have hray : ray ⊆ Kᶜ := by
    rintro z ⟨t, ht, rfl⟩ hz
    have htn : (R + 1) / ‖v‖ ≤ t := (le_max_right ..).trans ht
    have htpos : 0 ≤ t := ht₀.trans ht
    have hnorm : ‖t • v‖ = t * ‖v‖ := by simp [norm_smul, abs_of_nonneg htpos]
    have hbound := hR (t • v) hz
    rw [hnorm] at hbound
    have := (div_le_iff₀ hvpos).mp htn
    linarith
  have hconn : IsPreconnected ray :=
    isPreconnected_Ici.image _ (continuous_id.smul continuous_const).continuousOn
  have hmem : t₀ • v ∈ ray := ⟨t₀, self_mem_Ici, rfl⟩
  refine ⟨t₀ • v, hray hmem, ?_⟩
  have hsub := hconn.subset_connectedComponentIn hmem hray
  intro hb
  obtain ⟨B, hB⟩ := hb.exists_norm_le
  let t : ℝ := max t₀ ((B + 1) / ‖v‖)
  have ht : t₀ ≤ t := le_max_left ..
  have htn : (B + 1) / ‖v‖ ≤ t := le_max_right ..
  have htpos : 0 ≤ t := ht₀.trans ht
  have hnorm : ‖t • v‖ = t * ‖v‖ := by simp [norm_smul, abs_of_nonneg htpos]
  have hbound := hB (t • v) (hsub ⟨t, ht, rfl⟩)
  rw [hnorm] at hbound
  have := (div_le_iff₀ hvpos).mp htn
  linarith

/-- Every unbounded complementary component of a bounded set meets the same large sphere. -/
theorem unbounded_connectedComponentIn_compl_eq {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E} (hK : IsBounded K) (hdim : 1 < Module.rank ℝ E) {x y : E}
    (hx : ¬ IsBounded (connectedComponentIn Kᶜ x))
    (hy : ¬ IsBounded (connectedComponentIn Kᶜ y)) :
    connectedComponentIn Kᶜ x = connectedComponentIn Kᶜ y := by
  obtain ⟨R, hR⟩ := hK.exists_norm_le
  have hcx : x ∈ connectedComponentIn Kᶜ x := by
    apply mem_connectedComponentIn
    by_contra hxK
    exact hx ((connectedComponentIn_eq_empty hxK).symm ▸ isBounded_empty)
  have hcy : y ∈ connectedComponentIn Kᶜ y := by
    apply mem_connectedComponentIn
    by_contra hyK
    exact hy ((connectedComponentIn_eq_empty hyK).symm ▸ isBounded_empty)
  let r : ℝ := max (max (‖x‖) (‖y‖)) R + 1
  have hrx : ‖x‖ ≤ r := by
    dsimp [r]
    linarith [le_max_left (‖x‖) (‖y‖), le_max_left (max (‖x‖) (‖y‖)) R]
  have hry : ‖y‖ ≤ r := by
    dsimp [r]
    linarith [le_max_right (‖x‖) (‖y‖), le_max_left (max (‖x‖) (‖y‖)) R]
  have hrK : R < r := by dsimp [r]; linarith [le_max_right (max (‖x‖) (‖y‖)) R]
  have hr0 : 0 ≤ r := by linarith [norm_nonneg x, hrx]
  have hsph : Metric.sphere (0 : E) r ⊆ Kᶜ := by
    intro z hz hzK
    have hzR := hR z hzK
    have hzn : ‖z‖ = r := by simpa [Metric.mem_sphere, dist_zero_right] using hz
    linarith
  have hmeet (w : E) (hw : w ∈ connectedComponentIn Kᶜ w)
      (hun : ¬ IsBounded (connectedComponentIn Kᶜ w)) (hwr : ‖w‖ ≤ r) :
      ∃ z ∈ connectedComponentIn Kᶜ w, z ∈ Metric.sphere (0 : E) r := by
    have : ∃ z ∈ connectedComponentIn Kᶜ w, r < ‖z‖ := by
      by_contra h
      apply hun
      exact (isBounded_iff_forall_norm_le).mpr
        ⟨r, by simpa only [not_exists, not_and, not_lt] using h⟩
    obtain ⟨z, hz, hzr⟩ := this
    obtain ⟨q, hq, hqn⟩ :=
      isPreconnected_connectedComponentIn.intermediate_value hw hz continuous_norm.continuousOn
        ⟨hwr, hzr.le⟩
    exact ⟨q, hq, by simpa [Metric.mem_sphere, dist_zero_right] using hqn⟩
  obtain ⟨a, ha, has⟩ := hmeet x hcx hx hrx
  obtain ⟨b, hb, hbs⟩ := hmeet y hcy hy hry
  have hS := (isPathConnected_sphere hdim (0 : E) hr0).isConnected.isPreconnected
  have hab : b ∈ connectedComponentIn Kᶜ a :=
    hS.subset_connectedComponentIn has hsph hbs
  have hba : b ∈ connectedComponentIn Kᶜ x := by
    rw [connectedComponentIn_eq ha]
    exact hab
  exact (connectedComponentIn_eq hba).trans (connectedComponentIn_eq hb).symm

/-- An unbounded complementary component of a bounded set has bounded complement. -/
theorem isBounded_compl_connectedComponentIn_compl {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {K : Set E} {x : E}
    (hK : IsBounded K) (hdim : 1 < Module.rank ℝ E)
    (hx : ¬ IsBounded (connectedComponentIn Kᶜ x)) :
    IsBounded (connectedComponentIn Kᶜ x)ᶜ := by
  obtain ⟨r, hr⟩ := hK.subset_closedBall (0 : E)
  obtain ⟨y, hy, hyr⟩ : ∃ y ∈ connectedComponentIn Kᶜ x,
      y ∉ Metric.closedBall (0 : E) r := by
    by_contra! h
    exact hx (Metric.isBounded_closedBall.subset h)
  have hsub : (Metric.closedBall (0 : E) r)ᶜ ⊆ Kᶜ := compl_subset_compl.mpr hr
  have hball := (isPreconnected_compl_closedBall hdim (0 : E) r).subset_connectedComponentIn
    hyr hsub
  rw [← connectedComponentIn_eq hy] at hball
  exact Metric.isBounded_closedBall.subset (compl_subset_comm.mp hball)

end Bornology
