module

public import Matroid.MiniTauCeti.JCT.Topology.PrimitiveLink
public import Matroid.MiniTauCeti.JCT.Topology.PlanarRetract
public import Mathlib.Analysis.Complex.Tietze

/-!
# The complement of a planar arc

Tietze extension extends the inverse of an arc parametrization to the plane. Composing it with
the parametrization gives a bounded retraction, whose complement is path connected.
-/

@[expose] public section

open Set Topology

namespace IsArc

/-- The complement of an arc in a real normed plane is path connected. -/
theorem isPathConnected_compl {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)] {A : Set E} (hA : IsArc A) : IsPathConnected Aᶜ := by
  let : FiniteDimensional ℝ E := .of_fact_finrank_eq_two
  let e : E ≃L[ℝ] ℂ := ContinuousLinearEquiv.ofFinrankEq
    ((Fact.out : Module.finrank ℝ E = 2).trans Complex.finrank_real_complex.symm)
  have hAc : IsCompact (e '' A) := hA.isCompact.image e.continuous
  obtain ⟨f, hf, hAeq⟩ := hA.image (f := ⟨e, e.continuous⟩) e.injective
  change range f = e '' A at hAeq
  have he : IsClosedEmbedding (f : unitInterval → ℂ) :=
    f.continuous.isClosedEmbedding hf
  obtain ⟨g, hgf⟩ := (ContinuousMap.id unitInterval).exists_extension he
  let r : C(ℂ, ℂ) := f.comp g
  have hrange : range r ⊆ e '' A := by
    rintro z ⟨w, rfl⟩
    rw [← hAeq]
    exact ⟨g w, rfl⟩
  have hfix : EqOn r id (e '' A) := by
    intro z hz
    obtain ⟨t, rfl⟩ : z ∈ range f := hAeq ▸ hz
    have hgf' : g.comp f = ContinuousMap.id unitInterval := by
      convert hgf
    have ht := congrArg (fun k : C(unitInterval, unitInterval) ↦ k t) hgf'
    change g (f t) = t at ht
    change f (g (f t)) = f t
    rw [ht]
  have hcompl := hAc.isBounded.isPathConnected_compl_of_retract r.continuous hrange hfix
  simpa only [preimage_compl, ContinuousLinearEquiv.coe_toHomeomorph,
    e.injective.preimage_image] using e.toHomeomorph.isPathConnected_preimage.mpr hcompl

end IsArc

namespace IsPrimitiveLink

/-- A primitive link with distinct endpoints has path-connected complement in the plane. -/
theorem isPathConnected_compl {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Fact (Module.finrank ℝ E = 2)] {A : Set E} {a b : E}
    (hA : IsPrimitiveLink A a b) (hab : a ≠ b) : IsPathConnected Aᶜ :=
  (hA.isArc hab).isPathConnected_compl

end IsPrimitiveLink
