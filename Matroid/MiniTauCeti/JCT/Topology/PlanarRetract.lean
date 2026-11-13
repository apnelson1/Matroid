module

public import Matroid.MiniTauCeti.JCT.Topology.ExteriorComponent
public import Matroid.MiniTauCeti.JCT.Topology.Circle
public import Matroid.MiniTauCeti.JCT.Topology.Homotopy.Contractible
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.Topology.Piecewise
public import Mathlib.Topology.Algebra.Module.LocallyConvex
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.Analysis.LocallyConvex.WithSeminorms

/-!
# Complements of bounded planar retracts

A bounded retract of the complex plane has path-connected complement. The proof excludes bounded
complementary components by constructing a retraction of the plane onto a circle. The circle
obstruction follows from its fundamental group.
-/

@[expose] public section

open Set Topology Metric

namespace Bornology.IsBounded

/-- The complement of a bounded planar retract is path connected. -/
theorem isPathConnected_compl_of_retract {K : Set ℂ} (hK : IsBounded K)
    {r : ℂ → ℂ} (hr : Continuous r) (hrange : range r ⊆ K)
    (hfix : EqOn r id K) : IsPathConnected Kᶜ := by
  classical
  have hKclosed : IsClosed K := by
    have heq : K = {z | r z = z} := by
      ext z
      constructor
      · intro hz
        exact hfix hz
      · intro hz
        rw [← hz]
        exact hrange ⟨z, rfl⟩
    rw [heq]
    exact isClosed_eq hr continuous_id
  have hcomp (p : ℂ) (hp : p ∉ K) :
      ¬ IsBounded (connectedComponentIn Kᶜ p) := by
    let U := connectedComponentIn Kᶜ p
    have hpU : p ∈ U := mem_connectedComponentIn hp
    intro hU
    obtain ⟨R, hR⟩ := hU.subset_ball p
    have hRpos : 0 < R := by
      have h := hR hpU
      simpa using h
    let g : ℂ → ℂ := U.piecewise r id
    have hfr : frontier U ⊆ K := hKclosed.frontier_connectedComponentIn_compl_subset
    have hg : Continuous g :=
      Continuous.piecewise (fun z hz ↦ hfix (hfr hz)) hr continuous_id
    have havoid (z : ℂ) : g z ≠ p := by
      by_cases hz : z ∈ U
      · have hzK : g z ∈ K := by
          change U.piecewise r id z ∈ K
          rw [piecewise_eq_of_mem (hi := hz)]
          exact hrange ⟨z, rfl⟩
        exact fun h ↦ hp (h ▸ hzK)
      · have hgz : g z = z := by simp [g, piecewise_eq_of_notMem (hi := hz)]
        exact fun h ↦ hz ((hgz.symm.trans h) ▸ hpU)
    let i : C(Circle, ℂ) := ⟨fun u ↦ p + R • (u : ℂ), by fun_prop⟩
    have houtside (u : Circle) : i u ∉ U := by
      intro hu
      have hball := hR hu
      have hnorm : ‖(i u) - p‖ = R := by
        simp [i, Real.norm_eq_abs, abs_of_pos hRpos]
      rw [Metric.mem_ball, dist_eq_norm, hnorm] at hball
      exact (lt_irrefl R) hball
    let q : ℂ → ℂ := fun z ↦ g z - p
    have hq (z : ℂ) : q z ≠ 0 := sub_ne_zero.mpr (havoid z)
    have hqc : Continuous q := hg.sub continuous_const
    let n : C(ℂ, Circle) :=
      ⟨fun z ↦ ⟨‖q z‖⁻¹ • q z, by
          apply mem_sphere_zero_iff_norm.mpr
          simp [norm_ne_zero_iff.mpr (hq z)]⟩,
        by
          apply Continuous.subtype_mk
          exact (hqc.norm.inv₀ fun z ↦ norm_ne_zero_iff.mpr (hq z)).smul hqc⟩
    have hni : n.comp i = ContinuousMap.id Circle := by
      ext u
      have hgi : g (i u) = i u := by simp [g, houtside u]
      have hqi : q (i u) = R • (u : ℂ) := by
        change g (i u) - p = R • (u : ℂ)
        rw [hgi]
        simp [i]
      change ‖q (i u)‖⁻¹ • q (i u) = (u : ℂ)
      rw [hqi]
      have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hRpos.ne'
      simp [Real.norm_eq_abs, abs_of_pos hRpos, hRc]
    exact Circle.not_contractibleSpace (ContractibleSpace.of_homotopy_retract i n (by rw [hni]))
  obtain ⟨x, hx, -⟩ := exists_unbounded_connectedComponentIn_compl hK
  have hall : Kᶜ = connectedComponentIn Kᶜ x := by
    apply Subset.antisymm
    · intro y hy
      have hxy := unbounded_connectedComponentIn_compl_eq hK
        (by rw [Complex.rank_real_complex]; norm_num) (hcomp y hy) (hcomp x hx)
      exact hxy ▸ mem_connectedComponentIn hy
    · exact connectedComponentIn_subset _ _
  apply hKclosed.isOpen_compl.isConnected_iff_isPathConnected.mp
  rw [hall]
  exact isConnected_connectedComponentIn_iff.mpr hx

end Bornology.IsBounded
