module

public import Matroid.MiniTauCeti.JCT.Topology.Circuit.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional

/-!
# Transporting complementary regions between real normed planes

A continuous linear equivalence transports the bounded-region conclusion for intrinsic
circuits from the complex plane to any two-dimensional real normed space.
-/

public section

open Set Topology Function Bornology

namespace Jordan

/-- The bounded-region conclusion for complex circuits gives the same conclusion in every
real normed plane, with no additional structure required from the caller. -/
theorem bounded_regions_of_complex
    (hcomplex : ∀ {C : Set ℂ}, IsCircuit C → IsCompact C →
      ∃ U : Set ℂ, U ⊆ Cᶜ ∧ IsBounded U ∧ IsConnected U ∧
        IsConnected (Cᶜ \ U) ∧ frontier U = C ∧ frontier (Cᶜ \ U) = C)
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)] {C : Set E} (hC : IsCircuit C) (hc : IsCompact C) :
    ∃ U : Set E, U ⊆ Cᶜ ∧ IsBounded U ∧ IsConnected U ∧
      IsConnected (Cᶜ \ U) ∧ frontier U = C ∧ frontier (Cᶜ \ U) = C := by
  let : FiniteDimensional ℝ E := .of_fact_finrank_eq_two
  let e : E ≃L[ℝ] ℂ := ContinuousLinearEquiv.ofFinrankEq
    ((Fact.out : Module.finrank ℝ E = 2).trans Complex.finrank_real_complex.symm)
  have heC : IsCircuit (e '' C) := e.toHomeomorph.isEmbedding.isCircuit_image.mpr hC
  obtain ⟨U, hU, hbU, hcU, hcV, hfU, hfV⟩ := hcomplex heC (hc.image e.continuous)
  have hpre : e ⁻¹' (e '' C) = C := e.injective.preimage_image C
  have hdiff : e ⁻¹' ((e '' C)ᶜ \ U) = Cᶜ \ e ⁻¹' U := by
    rw [preimage_sdiff, preimage_compl, hpre]
  refine ⟨e ⁻¹' U, ?_, ?_, e.toHomeomorph.isConnected_preimage.mpr hcU,
    hdiff ▸ e.toHomeomorph.isConnected_preimage.mpr hcV, ?_, ?_⟩
  · intro x hx hcx
    exact hU hx ⟨x, hcx, rfl⟩
  · change IsBounded (e.toHomeomorph ⁻¹' U)
    rw [← e.toHomeomorph.image_symm]
    exact e.symm.lipschitzWith.isBounded_image hbU
  · change frontier (e.toHomeomorph ⁻¹' U) = C
    rw [← e.toHomeomorph.preimage_frontier, hfU]
    exact hpre
  · rw [← hdiff]
    change frontier (e.toHomeomorph ⁻¹' ((e '' C)ᶜ \ U)) = C
    rw [← e.toHomeomorph.preimage_frontier, hfV]
    exact hpre

end Jordan
